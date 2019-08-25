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

section \<open>Complex numbers in Metamatah 1\<close> 

theory MMI_Complex_ZF_1 imports MMI_examples

begin  

text\<open>This theory contains theorems (with proofs) about complex numbers
  imported from the Metamath's set.mm database. 
  The original Metamath proofs were mostly written by Norman Megill, 
  see the Metamath Proof Explorer pages for full atribution.
  This theory contains about 200 theorems.
\<close>

(********211-220*************************)

lemma (in MMIsar0) MMI_recrect: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) = A"
proof -
   have S1: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) )" by (rule MMI_opreq2)
   from S1 have S2: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) = 
 ( \<one> \<cdiv> ( \<one> \<cdiv> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) ) )" 
     by (rule MMI_opreq2d)
   have S3: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 A = if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> )" by (rule MMI_id)
   from S2 S3 have S4: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) = 
 A \<longleftrightarrow> 
 ( \<one> \<cdiv> ( \<one> \<cdiv> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) ) ) = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) )" by (rule MMI_eqeq12d)
   have S5: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( A \<in> \<complex> \<longleftrightarrow> 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex> )" by (rule MMI_eleq1)
   have S6: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   from S5 S6 have S7: "A = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longleftrightarrow> 
 ( if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex> \<and> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero> ) )" by (rule MMI_anbi12d)
   have S8: "\<one> = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( \<one> \<in> \<complex> \<longleftrightarrow> 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex> )" by (rule MMI_eleq1)
   have S9: "\<one> = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( \<one> \<noteq> \<zero> \<longleftrightarrow> 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   from S8 S9 have S10: "\<one> = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<longrightarrow> 
 ( ( \<one> \<in> \<complex> \<and> \<one> \<noteq> \<zero> ) \<longleftrightarrow> 
 ( if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex> \<and> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero> ) )" by (rule MMI_anbi12d)
   have S11: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S12: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from S11 S12 have S13: "\<one> \<in> \<complex> \<and> \<one> \<noteq> \<zero>" by (rule MMI_pm3_2i)
   from S7 S10 S13 have S14: "if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex> \<and> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimhyp)
   from S14 have S15: "if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex>" by (rule MMI_pm3_26i)
   from S14 have S16: "if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<in> \<complex> \<and> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero>" .
   from S16 have S17: "if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) \<noteq> \<zero>" by (rule MMI_pm3_27i)
   from S15 S17 have S18: "( \<one> \<cdiv> ( \<one> \<cdiv> if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> ) ) ) = 
 if ( ( A \<in> \<complex> \<and> A \<noteq> \<zero> ) , A , \<one> )" by (rule MMI_recrec)
   from S4 S18 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) = A" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_rec11i: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>" and
    A4: "B \<noteq> \<zero>"   
   shows "( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B ) \<longleftrightarrow> A = B"
proof -
   have S1: "( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> B ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> A ) ) = 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_opreq2)
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "B \<in> \<complex>".
   from A1 have S4: "A \<in> \<complex>".
   from A3 have S5: "A \<noteq> \<zero>".
   from S4 S5 have S6: "( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_reccl)
   from S2 S3 S6 have S7: "( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> A ) ) = 
 ( ( A \<cdot> ( \<one> \<cdiv> A ) ) \<cdot> B )" by (rule MMI_mul23)
   from A1 have S8: "A \<in> \<complex>".
   from A3 have S9: "A \<noteq> \<zero>".
   from S8 S9 have S10: "( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_recid)
   from S10 have S11: "( ( A \<cdot> ( \<one> \<cdiv> A ) ) \<cdot> B ) = ( \<one> \<cdot> B )" by (rule MMI_opreq1i)
   from A2 have S12: "B \<in> \<complex>".
   from S12 have S13: "( \<one> \<cdot> B ) = B" by (rule MMI_mulid2)
   from S7 S11 S13 have S14: "( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> A ) ) = B" by (rule MMI_3eqtr)
   from A1 have S15: "A \<in> \<complex>".
   from A2 have S16: "B \<in> \<complex>".
   from A2 have S17: "B \<in> \<complex>".
   from A4 have S18: "B \<noteq> \<zero>".
   from S17 S18 have S19: "( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_reccl)
   from S15 S16 S19 have S20: "( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( A \<cdot> ( B \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_mulass)
   from A2 have S21: "B \<in> \<complex>".
   from A4 have S22: "B \<noteq> \<zero>".
   from S21 S22 have S23: "( B \<cdot> ( \<one> \<cdiv> B ) ) = \<one>" by (rule MMI_recid)
   from S23 have S24: "( A \<cdot> ( B \<cdot> ( \<one> \<cdiv> B ) ) ) = ( A \<cdot> \<one> )" by (rule MMI_opreq2i)
   from A1 have S25: "A \<in> \<complex>".
   from S25 have S26: "( A \<cdot> \<one> ) = A" by (rule MMI_mulid1)
   from S20 S24 S26 have S27: "( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> B ) ) = A" by (rule MMI_3eqtr)
   from S14 S27 have S28: "( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> A ) ) = 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> B ) ) \<longleftrightarrow> B = A" by (rule MMI_eqeq12i)
   have S29: "B = A \<longleftrightarrow> A = B" by (rule MMI_eqcom)
   from S28 S29 have S30: "( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> A ) ) = 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> B ) ) \<longleftrightarrow> A = B" by (rule MMI_bitr)
   from S1 S30 have S31: "( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B ) \<longrightarrow> A = B" by (rule MMI_sylib)
   have S32: "A = B \<longrightarrow> ( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B )" by (rule MMI_opreq2)
   from S31 S32 show "( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B ) \<longleftrightarrow> A = B" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_rec11: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B ) \<longleftrightarrow> A = B )"
proof -
   have S1: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) )" by (rule MMI_opreq2)
   from S1 have S2: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> B ) \<longleftrightarrow> 
 ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 ( \<one> \<cdiv> B ) )" by (rule MMI_eqeq1d)
   have S3: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( A = B \<longleftrightarrow> if ( A \<noteq> \<zero> , A , \<one> ) = B )" by (rule MMI_eqeq1)
   from S2 S3 have S4: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( ( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B ) \<longleftrightarrow> A = B ) \<longleftrightarrow> 
 ( ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 ( \<one> \<cdiv> B ) \<longleftrightarrow> 
 if ( A \<noteq> \<zero> , A , \<one> ) = B ) )" by (rule MMI_bibi12d)
   have S5: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( \<one> \<cdiv> B ) = 
 ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_opreq2)
   from S5 have S6: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 ( \<one> \<cdiv> B ) \<longleftrightarrow> 
 ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) )" by (rule MMI_eqeq2d)
   have S7: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( if ( A \<noteq> \<zero> , A , \<one> ) = 
 B \<longleftrightarrow> 
 if ( A \<noteq> \<zero> , A , \<one> ) = 
 if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_eqeq2)
   from S6 S7 have S8: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = ( \<one> \<cdiv> B ) \<longleftrightarrow> if ( A \<noteq> \<zero> , A , \<one> ) = B ) \<longleftrightarrow> 
 ( ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) \<longleftrightarrow> 
 if ( A \<noteq> \<zero> , A , \<one> ) = 
 if ( B \<noteq> \<zero> , B , \<one> ) ) )" by (rule MMI_bibi12d)
   from A1 have S9: "A \<in> \<complex>".
   have S10: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S9 S10 have S11: "if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   from A2 have S12: "B \<in> \<complex>".
   have S13: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S12 S13 have S14: "if ( B \<noteq> \<zero> , B , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   have S15: "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   have S16: "if ( B \<noteq> \<zero> , B , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S11 S14 S15 S16 have S17: "( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) \<longleftrightarrow> 
 if ( A \<noteq> \<zero> , A , \<one> ) = 
 if ( B \<noteq> \<zero> , B , \<one> )" by (rule MMI_rec11i)
   from S4 S8 S17 show "( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) = ( \<one> \<cdiv> B ) \<longleftrightarrow> A = B )" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_divmuldivt: 
   shows "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )"
proof -
   have S1: "( ( B \<cdot> D ) \<in> \<complex> \<and> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) \<in> \<complex> \<and> ( B \<cdot> D ) \<noteq> \<zero> ) \<longrightarrow> 
 ( ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) )" by (rule MMI_divcan3t)
   have S2: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_ad2ant2l)
   from S3 have S4: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_adantr)
   have S5: "( ( A \<cdiv> B ) \<in> \<complex> \<and> ( C \<cdiv> D ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) \<in> \<complex>" by (rule MMI_axmulcl)
   have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_divclt)
   from S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_3expa)
   have S8: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_divclt)
   from S8 have S9: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_3expa)
   from S5 S7 S9 have S10: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<and> ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) \<in> \<complex>" by (rule MMI_syl2an)
   from S10 have S11: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) \<in> \<complex>" by (rule MMI_an4s)
   have S12: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( B \<cdot> D ) \<noteq> \<zero> )" by (rule MMI_muln0bt)
   from S12 have S13: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longrightarrow> ( B \<cdot> D ) \<noteq> \<zero> )" by (rule MMI_biimpd)
   from S13 have S14: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longrightarrow> ( B \<cdot> D ) \<noteq> \<zero> )" by (rule MMI_ad2ant2l)
   from S14 have S15: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdot> D ) \<noteq> \<zero>" by (rule MMI_imp)
   from S1 S4 S11 S15 have S16: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) )" by (rule MMI_syl3anc)
   have S17: "( ( B \<in> \<complex> \<and> ( A \<cdiv> B ) \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> ( C \<cdiv> D ) \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<cdot> ( A \<cdiv> B ) ) \<cdot> ( D \<cdot> ( C \<cdiv> D ) ) ) = 
 ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) )" by (rule MMI_mul4t)
   have S18: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   from S6 have S19: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" .
   from S18 S19 have S20: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<in> \<complex> \<and> ( A \<cdiv> B ) \<in> \<complex> )" by (rule MMI_jca)
   from S20 have S21: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<in> \<complex> \<and> ( A \<cdiv> B ) \<in> \<complex> )" by (rule MMI_3expa)
   have S22: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> D \<in> \<complex>" by (rule MMI_pm3_27)
   from S22 have S23: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> D \<in> \<complex>" by (rule MMI_adantr)
   from S9 have S24: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" .
   from S23 S24 have S25: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<in> \<complex> \<and> ( C \<cdiv> D ) \<in> \<complex> )" by (rule MMI_jca)
   from S17 S21 S25 have S26: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<and> ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdot> ( A \<cdiv> B ) ) \<cdot> ( D \<cdot> ( C \<cdiv> D ) ) ) = 
 ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) )" by (rule MMI_syl2an)
   have S27: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdot> ( A \<cdiv> B ) ) = A" by (rule MMI_divcan2t)
   from S27 have S28: "B \<in> \<complex> \<longrightarrow> 
 ( A \<in> \<complex> \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> ( B \<cdot> ( A \<cdiv> B ) ) = A ) )" by (rule MMI_3exp)
   from S28 have S29: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> ( B \<cdot> ( A \<cdiv> B ) ) = A )" by (rule MMI_impcom)
   from S29 have S30: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdot> ( A \<cdiv> B ) ) = A" by (rule MMI_imp)
   have S31: "( D \<in> \<complex> \<and> C \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<cdot> ( C \<cdiv> D ) ) = C" by (rule MMI_divcan2t)
   from S31 have S32: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<cdot> ( C \<cdiv> D ) ) = C" by (rule MMI_3com12)
   from S32 have S33: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<cdot> ( C \<cdiv> D ) ) = C" by (rule MMI_3expa)
   from S30 S33 have S34: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<and> ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdot> ( A \<cdiv> B ) ) \<cdot> ( D \<cdot> ( C \<cdiv> D ) ) ) = 
 ( A \<cdot> C )" by (rule MMI_opreqan12d)
   from S26 S34 have S35: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<and> ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) ) = 
 ( A \<cdot> C )" by (rule MMI_eqtr3d)
   from S35 have S36: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) ) = 
 ( A \<cdot> C )" by (rule MMI_an4s)
   from S36 have S37: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( ( B \<cdot> D ) \<cdot> ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_opreq1d)
   from S16 S37 show "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_divcan5t: 
   shows "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdot> A ) \<cdiv> ( C \<cdot> B ) ) = ( A \<cdiv> B )"
proof -
   have S1: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> ( C \<cdiv> C ) = \<one>" by (rule MMI_dividt)
   from S1 have S2: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( C \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( \<one> \<cdot> ( A \<cdiv> B ) )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( \<one> \<cdot> ( A \<cdiv> B ) )" by (rule MMI_3ad2ant3)
   have S4: "( ( ( C \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> B \<in> \<complex> ) ) \<and> ( C \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( C \<cdot> B ) )" by (rule MMI_divmuldivt)
   have S5: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_pm3_26)
   from S5 have S6: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> C \<in> \<complex>" .
   from S5 S6 have S7: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> ( C \<in> \<complex> \<and> C \<in> \<complex> )" by (rule MMI_jca)
   have S8: "( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_pm3_26)
   from S8 have S9: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( A \<in> \<complex> \<and> B \<in> \<complex> )" by (rule MMI_anim2i)
   from S7 S9 have S10: "( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<and> ( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> B \<in> \<complex> ) )" by (rule MMI_anim12i)
   from S10 have S11: "( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<and> A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> B \<in> \<complex> ) )" by (rule MMI_3impb)
   from S11 have S12: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> B \<in> \<complex> ) )" by (rule MMI_3coml)
   have S13: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_pm3_27)
   have S14: "( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_pm3_27)
   from S13 S14 have S15: "( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<and> B \<noteq> \<zero> )" by (rule MMI_anim12i)
   from S15 have S16: "( ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<and> B \<noteq> \<zero> )" by (rule MMI_ancoms)
   from S16 have S17: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<and> B \<noteq> \<zero> )" by (rule MMI_3adant1)
   from S4 S12 S17 have S18: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( C \<cdot> B ) )" by (rule MMI_sylanc)
   have S19: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_divclt)
   from S19 have S20: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_3expb)
   have S21: "( A \<cdiv> B ) \<in> \<complex> \<longrightarrow> 
 ( \<one> \<cdot> ( A \<cdiv> B ) ) = ( A \<cdiv> B )" by (rule MMI_mulid2t)
   from S20 S21 have S22: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( \<one> \<cdot> ( A \<cdiv> B ) ) = ( A \<cdiv> B )" by (rule MMI_syl)
   from S22 have S23: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( \<one> \<cdot> ( A \<cdiv> B ) ) = ( A \<cdiv> B )" by (rule MMI_3adant3)
   from S3 S18 S23 show "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdot> A ) \<cdiv> ( C \<cdot> B ) ) = ( A \<cdiv> B )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_divmul13t: 
   shows "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> C ) = ( C \<cdot> A )" by (rule MMI_axmulcom)
   from S1 have S2: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<cdot> C ) = ( C \<cdot> A )" by (rule MMI_ad2ant2r)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_opreq1d)
   from S3 have S4: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_adantr)
   have S5: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldivt)
   have S6: "( ( ( C \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldivt)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longleftrightarrow> ( B \<in> \<complex> \<and> A \<in> \<complex> )" by (rule MMI_ancom)
   from S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( B \<in> \<complex> \<and> A \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) )" by (rule MMI_anbi1i)
   have S9: "( ( B \<in> \<complex> \<and> A \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> A \<in> \<complex> ) )" by (rule MMI_ancom)
   have S10: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> A \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( C \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> D \<in> \<complex> ) )" by (rule MMI_an42)
   from S8 S9 S10 have S11: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( C \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> D \<in> \<complex> ) )" by (rule MMI_3bitr)
   from S6 S11 have S12: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_sylanb)
   from S4 S5 S12 show "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_divmul24t: 
   shows "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdiv> D ) \<cdot> ( C \<cdiv> B ) )"
proof -
   have S1: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( B \<cdot> D ) = ( D \<cdot> B )" by (rule MMI_axmulcom)
   from S1 have S2: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> D ) = ( D \<cdot> B )" by (rule MMI_ad2ant2l)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( D \<cdot> B ) )" by (rule MMI_opreq2d)
   from S3 have S4: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( D \<cdot> B ) )" by (rule MMI_adantr)
   have S5: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldivt)
   have S6: "( ( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> B \<in> \<complex> ) ) \<and> ( D \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> D ) \<cdot> ( C \<cdiv> B ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( D \<cdot> B ) )" by (rule MMI_divmuldivt)
   have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> B \<in> \<complex> ) )" by (rule MMI_an42)
   have S8: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> B \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> B \<in> \<complex> ) )" by (rule MMI_an4)
   from S7 S8 have S9: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longleftrightarrow> 
 ( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> B \<in> \<complex> ) )" by (rule MMI_bitr)
   have S10: "( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( D \<noteq> \<zero> \<and> B \<noteq> \<zero> )" by (rule MMI_ancom)
   from S6 S9 S10 have S11: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> D ) \<cdot> ( C \<cdiv> B ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( D \<cdot> B ) )" by (rule MMI_syl2anb)
   from S4 S5 S11 show "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdiv> D ) \<cdot> ( C \<cdiv> B ) )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_divadddivt: 
   shows "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<ca> ( C \<cdiv> D ) ) = 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) )"
proof -
   have S1: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( B \<cdot> D ) \<noteq> \<zero> )" by (rule MMI_muln0bt)
   from S1 have S2: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( B \<cdot> D ) \<noteq> \<zero> )" by (rule MMI_ad2ant2l)
   have S3: "( ( ( A \<cdot> D ) \<in> \<complex> \<and> ( B \<cdot> C ) \<in> \<complex> \<and> ( B \<cdot> D ) \<in> \<complex> ) \<and> ( B \<cdot> D ) \<noteq> \<zero> ) \<longrightarrow> 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) \<ca> ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) )" by (rule MMI_divdirt)
   from S3 have S4: "( ( A \<cdot> D ) \<in> \<complex> \<and> ( B \<cdot> C ) \<in> \<complex> \<and> ( B \<cdot> D ) \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<cdot> D ) \<noteq> \<zero> \<longrightarrow> 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) \<ca> ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) ) )" by (rule MMI_ex)
   have S5: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S5 have S6: "( A \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantrl)
   from S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantlr)
   have S8: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S8 have S9: "( B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantrr)
   from S9 have S10: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantll)
   have S11: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S11 have S12: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_ad2ant2l)
   from S4 S7 S10 S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<cdot> D ) \<noteq> \<zero> \<longrightarrow> 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) \<ca> ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) ) )" by (rule MMI_syl3anc)
   from S2 S13 have S14: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) \<ca> ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) ) )" by (rule MMI_sylbid)
   from S14 have S15: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) \<ca> ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) )" by (rule MMI_imp)
   have S16: "( D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> ( D \<cdiv> D ) = \<one>" by (rule MMI_dividt)
   from S16 have S17: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( D \<cdiv> D ) = \<one>" by (rule MMI_ad2ant2l)
   from S17 have S18: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( D \<cdiv> D ) = \<one>" by (rule MMI_adantll)
   from S18 have S19: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> D ) ) = 
 ( ( A \<cdiv> B ) \<cdot> \<one> )" by (rule MMI_opreq2d)
   have S20: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldivt)
   have S21: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> D \<in> \<complex>" by (rule MMI_pm3_27)
   from S21 have S22: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> D \<in> \<complex>" .
   from S21 S22 have S23: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<in> \<complex> \<and> D \<in> \<complex> )" by (rule MMI_jca)
   from S20 S23 have S24: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_sylanl2)
   have S25: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_divclt)
   from S25 have S26: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_3expa)
   have S27: "( A \<cdiv> B ) \<in> \<complex> \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> \<one> ) = ( A \<cdiv> B )" by (rule MMI_ax1id)
   from S26 S27 have S28: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> \<one> ) = ( A \<cdiv> B )" by (rule MMI_syl)
   from S28 have S29: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> \<one> ) = ( A \<cdiv> B )" by (rule MMI_ad2ant2r)
   from S19 S24 S29 have S30: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) = ( A \<cdiv> B )" by (rule MMI_3eqtr3d)
   have S31: "( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> ( B \<cdiv> B ) = \<one>" by (rule MMI_dividt)
   from S31 have S32: "( B \<in> \<complex> \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdiv> B ) = \<one>" by (rule MMI_adantrr)
   from S32 have S33: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdiv> B ) = \<one>" by (rule MMI_adantll)
   from S33 have S34: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdiv> B ) = \<one>" by (rule MMI_adantlr)
   from S34 have S35: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( \<one> \<cdot> ( C \<cdiv> D ) )" by (rule MMI_opreq1d)
   have S36: "( ( ( B \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldivt)
   have S37: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_pm3_27)
   from S37 have S38: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" .
   from S37 S38 have S39: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( B \<in> \<complex> \<and> B \<in> \<complex> )" by (rule MMI_jca)
   from S36 S39 have S40: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_sylanl1)
   have S41: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_divclt)
   from S41 have S42: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_3expa)
   have S43: "( C \<cdiv> D ) \<in> \<complex> \<longrightarrow> 
 ( \<one> \<cdot> ( C \<cdiv> D ) ) = ( C \<cdiv> D )" by (rule MMI_mulid2t)
   from S42 S43 have S44: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdot> ( C \<cdiv> D ) ) = ( C \<cdiv> D )" by (rule MMI_syl)
   from S44 have S45: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( \<one> \<cdot> ( C \<cdiv> D ) ) = ( C \<cdiv> D )" by (rule MMI_ad2ant2l)
   from S35 S40 S45 have S46: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) = ( C \<cdiv> D )" by (rule MMI_3eqtr3d)
   from S30 S46 have S47: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> D ) ) \<ca> ( ( B \<cdot> C ) \<cdiv> ( B \<cdot> D ) ) ) = 
 ( ( A \<cdiv> B ) \<ca> ( C \<cdiv> D ) )" by (rule MMI_opreq12d)
   from S15 S47 show "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<ca> ( C \<cdiv> D ) ) = 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_eqtr2d)
qed

lemma (in MMIsar0) MMI_divdivdivt: 
   shows "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )"
proof -
   have S1: "( ( D \<cdiv> C ) \<in> \<complex> \<and> ( A \<cdiv> B ) \<in> \<complex> ) \<longrightarrow> 
 ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> C ) )" by (rule MMI_axmulcom)
   have S2: "( D \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S2 have S3: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<cdiv> C ) \<in> \<complex>" by (rule MMI_3com12)
   from S3 have S4: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( D \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S4 have S5: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( D \<cdiv> C ) \<in> \<complex>" by (rule MMI_adantrr)
   from S5 have S6: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( D \<cdiv> C ) \<in> \<complex>" by (rule MMI_ad2ant2l)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_divclt)
   from S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_3expa)
   from S8 have S9: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_ad2ant2r)
   from S1 S6 S9 have S10: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> C ) )" by (rule MMI_sylanc)
   have S11: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> C \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> C ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_divmuldivt)
   have S12: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<in> \<complex> \<and> C \<in> \<complex> )" by (rule MMI_pm3_22)
   from S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> C \<in> \<complex> ) )" by (rule MMI_anim2i)
   have S14: "( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_pm3_26)
   from S14 have S15: "( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> )" by (rule MMI_anim2i)
   from S11 S13 S15 have S16: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( D \<cdiv> C ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_syl2an)
   from S10 S16 have S17: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_eqtrd)
   from S17 have S18: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) ) = 
 ( ( C \<cdiv> D ) \<cdot> ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) )" by (rule MMI_opreq2d)
   from S12 have S19: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<in> \<complex> \<and> C \<in> \<complex> )" .
   from S19 have S20: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> C \<in> \<complex> ) )" by (rule MMI_ancli)
   have S21: "( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longrightarrow> ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> )" by (rule MMI_pm3_22)
   from S21 have S22: "( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> )" by (rule MMI_adantl)
   from S20 S22 have S23: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> C \<in> \<complex> ) ) \<and> ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> ) )" by (rule MMI_anim12i)
   from S23 have S24: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> C \<in> \<complex> ) ) \<and> ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> ) )" by (rule MMI_adantll)
   have S25: "( ( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( D \<in> \<complex> \<and> C \<in> \<complex> ) ) \<and> ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( D \<cdiv> C ) ) = 
 ( ( C \<cdot> D ) \<cdiv> ( D \<cdot> C ) )" by (rule MMI_divmuldivt)
   from S24 S25 have S26: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( D \<cdiv> C ) ) = 
 ( ( C \<cdot> D ) \<cdiv> ( D \<cdot> C ) )" by (rule MMI_syl)
   have S27: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( C \<cdot> D ) = ( D \<cdot> C )" by (rule MMI_axmulcom)
   from S27 have S28: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( C \<cdot> D ) = ( D \<cdot> C )" by (rule MMI_ad2antlr)
   from S28 have S29: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<cdot> D ) \<cdiv> ( D \<cdot> C ) ) = 
 ( ( D \<cdot> C ) \<cdiv> ( D \<cdot> C ) )" by (rule MMI_opreq1d)
   have S30: "( ( D \<cdot> C ) \<in> \<complex> \<and> ( D \<cdot> C ) \<noteq> \<zero> ) \<longrightarrow> 
 ( ( D \<cdot> C ) \<cdiv> ( D \<cdot> C ) ) = \<one>" by (rule MMI_dividt)
   have S31: "( D \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( D \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S31 have S32: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<cdot> C ) \<in> \<complex>" by (rule MMI_ancoms)
   from S32 have S33: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( D \<cdot> C ) \<in> \<complex>" by (rule MMI_ad2antlr)
   have S34: "( D \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longleftrightarrow> ( D \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_muln0bt)
   have S35: "( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( D \<noteq> \<zero> \<and> C \<noteq> \<zero> )" by (rule MMI_ancom)
   from S34 S35 have S36: "( D \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( D \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_syl5bb)
   from S36 have S37: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> ( D \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_ancoms)
   from S37 have S38: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( D \<cdot> C ) \<noteq> \<zero>" by (rule MMI_biimpa)
   from S38 have S39: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( D \<cdot> C ) \<noteq> \<zero>" by (rule MMI_ad2ant2l)
   from S30 S33 S39 have S40: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( D \<cdot> C ) \<cdiv> ( D \<cdot> C ) ) = \<one>" by (rule MMI_sylanc)
   from S26 S29 S40 have S41: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( D \<cdiv> C ) ) = \<one>" by (rule MMI_3eqtrd)
   from S41 have S42: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( ( C \<cdiv> D ) \<cdot> ( D \<cdiv> C ) ) \<cdot> ( A \<cdiv> B ) ) = 
 ( \<one> \<cdot> ( A \<cdiv> B ) )" by (rule MMI_opreq1d)
   have S43: "( ( C \<cdiv> D ) \<in> \<complex> \<and> ( D \<cdiv> C ) \<in> \<complex> \<and> ( A \<cdiv> B ) \<in> \<complex> ) \<longrightarrow> 
 ( ( ( C \<cdiv> D ) \<cdot> ( D \<cdiv> C ) ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( C \<cdiv> D ) \<cdot> ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) )" by (rule MMI_axmulass)
   have S44: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_divclt)
   from S44 have S45: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_3expa)
   from S45 have S46: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_adantrl)
   from S46 have S47: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" by (rule MMI_ad2ant2l)
   from S6 have S48: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( D \<cdiv> C ) \<in> \<complex>" .
   from S9 have S49: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" .
   from S43 S47 S48 S49 have S50: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( ( C \<cdiv> D ) \<cdot> ( D \<cdiv> C ) ) \<cdot> ( A \<cdiv> B ) ) = 
 ( ( C \<cdiv> D ) \<cdot> ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) )" by (rule MMI_syl3anc)
   from S9 have S51: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" .
   have S52: "( A \<cdiv> B ) \<in> \<complex> \<longrightarrow> 
 ( \<one> \<cdot> ( A \<cdiv> B ) ) = ( A \<cdiv> B )" by (rule MMI_mulid2t)
   from S51 S52 have S53: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( \<one> \<cdot> ( A \<cdiv> B ) ) = ( A \<cdiv> B )" by (rule MMI_syl)
   from S42 S50 S53 have S54: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( ( D \<cdiv> C ) \<cdot> ( A \<cdiv> B ) ) ) = 
 ( A \<cdiv> B )" by (rule MMI_3eqtr3d)
   from S18 S54 have S55: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) ) = 
 ( A \<cdiv> B )" by (rule MMI_eqtr3d)
   have S56: "( ( ( A \<cdiv> B ) \<in> \<complex> \<and> ( C \<cdiv> D ) \<in> \<complex> \<and> ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) \<in> \<complex> ) \<and> ( C \<cdiv> D ) \<noteq> \<zero> ) \<longrightarrow> 
 ( ( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) \<longleftrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) ) = 
 ( A \<cdiv> B ) )" by (rule MMI_divmult)
   from S9 have S57: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" .
   from S47 have S58: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( C \<cdiv> D ) \<in> \<complex>" .
   have S59: "( ( A \<cdot> D ) \<in> \<complex> \<and> ( B \<cdot> C ) \<in> \<complex> \<and> ( B \<cdot> C ) \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) \<in> \<complex>" by (rule MMI_divclt)
   have S60: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S60 have S61: "( A \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantrl)
   from S61 have S62: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantlr)
   from S62 have S63: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantr)
   have S64: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S64 have S65: "( B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantrr)
   from S65 have S66: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantll)
   from S66 have S67: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantr)
   have S68: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longleftrightarrow> ( B \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_muln0bt)
   from S68 have S69: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longrightarrow> ( B \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_biimpd)
   from S14 have S70: "( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longrightarrow> C \<noteq> \<zero>" .
   from S69 S70 have S71: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_sylan2i)
   from S71 have S72: "( B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_adantrr)
   from S72 have S73: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<noteq> \<zero> )" by (rule MMI_adantll)
   from S73 have S74: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( B \<cdot> C ) \<noteq> \<zero>" by (rule MMI_imp)
   from S59 S63 S67 S74 have S75: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) \<in> \<complex>" by (rule MMI_syl3anc)
   from S57 S58 S75 have S76: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<in> \<complex> \<and> ( C \<cdiv> D ) \<in> \<complex> \<and> ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) \<in> \<complex> )" by (rule MMI_3jca)
   have S77: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longleftrightarrow> ( C \<cdiv> D ) \<noteq> \<zero> )" by (rule MMI_divne0bt)
   from S77 have S78: "( C \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> ( C \<cdiv> D ) \<noteq> \<zero> )" by (rule MMI_biimpd)
   from S78 have S79: "C \<in> \<complex> \<longrightarrow> 
 ( D \<in> \<complex> \<longrightarrow> 
 ( D \<noteq> \<zero> \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> ( C \<cdiv> D ) \<noteq> \<zero> ) ) )" by (rule MMI_3exp)
   from S79 have S80: "C \<in> \<complex> \<longrightarrow> 
 ( D \<in> \<complex> \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( D \<noteq> \<zero> \<longrightarrow> ( C \<cdiv> D ) \<noteq> \<zero> ) ) )" by (rule MMI_com34)
   from S80 have S81: "( ( C \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( C \<cdiv> D ) \<noteq> \<zero>" by (rule MMI_imp43)
   from S81 have S82: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( C \<cdiv> D ) \<noteq> \<zero>" by (rule MMI_ad2ant2l)
   from S56 S76 S82 have S83: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) \<longleftrightarrow> 
 ( ( C \<cdiv> D ) \<cdot> ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) ) ) = 
 ( A \<cdiv> B ) )" by (rule MMI_sylanc)
   from S55 S83 have S84: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_mpbird)
   have S85: "( B \<noteq> \<zero> \<and> C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) \<longleftrightarrow> 
 ( B \<noteq> \<zero> \<and> ( C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) )" by (rule MMI_3anass)
   from S84 S85 show "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_sylan2b)
qed

lemma (in MMIsar0) MMI_divmuldiv: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>" and
    A5: "B \<noteq> \<zero>" and
    A6: "D \<noteq> \<zero>"   
   shows "( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   from S3 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> )" by (rule MMI_pm3_2i)
   from A5 have S8: "B \<noteq> \<zero>".
   from A6 have S9: "D \<noteq> \<zero>".
   from S8 S9 have S10: "B \<noteq> \<zero> \<and> D \<noteq> \<zero>" by (rule MMI_pm3_2i)
   have S11: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldivt)
   from S7 S10 S11 show "( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_mp2an)
qed

(************221-230********************)

lemma (in MMIsar0) MMI_divmul13: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>" and
    A5: "B \<noteq> \<zero>" and
    A6: "D \<noteq> \<zero>"   
   shows "( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) )"
proof -
   from A3 have S1: "C \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( C \<cdot> A ) = ( A \<cdot> C )" by (rule MMI_mulcom)
   from S3 have S4: "( ( C \<cdot> A ) \<cdiv> ( B \<cdot> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_opreq1i)
   from A3 have S5: "C \<in> \<complex>".
   from A2 have S6: "B \<in> \<complex>".
   from A1 have S7: "A \<in> \<complex>".
   from A4 have S8: "D \<in> \<complex>".
   from A5 have S9: "B \<noteq> \<zero>".
   from A6 have S10: "D \<noteq> \<zero>".
   from S5 S6 S7 S8 S9 S10 have S11: "( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) ) = 
 ( ( C \<cdot> A ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldiv)
   from A1 have S12: "A \<in> \<complex>".
   from A2 have S13: "B \<in> \<complex>".
   from A3 have S14: "C \<in> \<complex>".
   from A4 have S15: "D \<in> \<complex>".
   from A5 have S16: "B \<noteq> \<zero>".
   from A6 have S17: "D \<noteq> \<zero>".
   from S12 S13 S14 S15 S16 S17 have S18: "( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> C ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divmuldiv)
   from S4 S11 S18 show "( ( A \<cdiv> B ) \<cdot> ( C \<cdiv> D ) ) = 
 ( ( C \<cdiv> B ) \<cdot> ( A \<cdiv> D ) )" by (rule MMI_3eqtr4r)
qed

lemma (in MMIsar0) MMI_divadddiv: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>" and
    A5: "B \<noteq> \<zero>" and
    A6: "D \<noteq> \<zero>"   
   shows "( ( A \<cdiv> B ) \<ca> ( C \<cdiv> D ) ) = 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   from S3 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> )" by (rule MMI_pm3_2i)
   from A5 have S8: "B \<noteq> \<zero>".
   from A6 have S9: "D \<noteq> \<zero>".
   from S8 S9 have S10: "B \<noteq> \<zero> \<and> D \<noteq> \<zero>" by (rule MMI_pm3_2i)
   have S11: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<ca> ( C \<cdiv> D ) ) = 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_divadddivt)
   from S7 S10 S11 show "( ( A \<cdiv> B ) \<ca> ( C \<cdiv> D ) ) = 
 ( ( ( A \<cdot> D ) \<ca> ( B \<cdot> C ) ) \<cdiv> ( B \<cdot> D ) )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_divdivdiv: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>" and
    A5: "B \<noteq> \<zero>" and
    A6: "D \<noteq> \<zero>" and
    A7: "C \<noteq> \<zero>"   
   shows "( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   from S3 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> )" by (rule MMI_pm3_2i)
   from A5 have S8: "B \<noteq> \<zero>".
   from A7 have S9: "C \<noteq> \<zero>".
   from A6 have S10: "D \<noteq> \<zero>".
   from S8 S9 S10 have S11: "B \<noteq> \<zero> \<and> C \<noteq> \<zero> \<and> D \<noteq> \<zero>" by (rule MMI_3pm3_2i)
   have S12: "( ( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> \<and> D \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_divdivdivt)
   from S7 S11 S12 show "( ( A \<cdiv> B ) \<cdiv> ( C \<cdiv> D ) ) = 
 ( ( A \<cdot> D ) \<cdiv> ( B \<cdot> C ) )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_recdivt: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( \<one> \<cdiv> ( A \<cdiv> B ) ) = ( B \<cdiv> A )"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S1 S2 have S3: "\<one> \<in> \<complex> \<and> \<one> \<in> \<complex>" by (rule MMI_pm3_2i)
   have S4: "( ( ( \<one> \<in> \<complex> \<and> \<one> \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> B \<in> \<complex> ) ) \<and> ( \<one> \<noteq> \<zero> \<and> A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( \<one> \<cdiv> \<one> ) \<cdiv> ( A \<cdiv> B ) ) = 
 ( ( \<one> \<cdot> B ) \<cdiv> ( \<one> \<cdot> A ) )" by (rule MMI_divdivdivt)
   have S5: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from S5 have S6: "( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<noteq> \<zero> \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) )" by (rule MMI_jctl)
   have S7: "( \<one> \<noteq> \<zero> \<and> A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longleftrightarrow> 
 ( \<one> \<noteq> \<zero> \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) )" by (rule MMI_3anass)
   from S6 S7 have S8: "( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<noteq> \<zero> \<and> A \<noteq> \<zero> \<and> B \<noteq> \<zero> )" by (rule MMI_sylibr)
   from S4 S8 have S9: "( ( ( \<one> \<in> \<complex> \<and> \<one> \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> B \<in> \<complex> ) ) \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( \<one> \<cdiv> \<one> ) \<cdiv> ( A \<cdiv> B ) ) = 
 ( ( \<one> \<cdot> B ) \<cdiv> ( \<one> \<cdot> A ) )" by (rule MMI_sylan2)
   from S3 S9 have S10: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( \<one> \<cdiv> \<one> ) \<cdiv> ( A \<cdiv> B ) ) = 
 ( ( \<one> \<cdot> B ) \<cdiv> ( \<one> \<cdot> A ) )" by (rule MMI_mpanl1)
   have S11: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S11 have S12: "( \<one> \<cdiv> \<one> ) = \<one>" by (rule MMI_div1)
   from S12 have S13: "( ( \<one> \<cdiv> \<one> ) \<cdiv> ( A \<cdiv> B ) ) = 
 ( \<one> \<cdiv> ( A \<cdiv> B ) )" by (rule MMI_opreq1i)
   from S13 have S14: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( \<one> \<cdiv> \<one> ) \<cdiv> ( A \<cdiv> B ) ) = 
 ( \<one> \<cdiv> ( A \<cdiv> B ) )" by (rule MMI_a1i)
   have S15: "B \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> B ) = B" by (rule MMI_mulid2t)
   have S16: "A \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> A ) = A" by (rule MMI_mulid2t)
   from S15 S16 have S17: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( \<one> \<cdot> B ) \<cdiv> ( \<one> \<cdot> A ) ) = ( B \<cdiv> A )" by (rule MMI_opreqan12rd)
   from S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( \<one> \<cdot> B ) \<cdiv> ( \<one> \<cdot> A ) ) = ( B \<cdiv> A )" by (rule MMI_adantr)
   from S10 S14 S18 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( \<one> \<cdiv> ( A \<cdiv> B ) ) = ( B \<cdiv> A )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_divdiv23t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )"
proof -
   have S1: "( ( A \<in> \<complex> \<and> ( \<one> \<cdiv> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_div23t)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 A \<in> \<complex>" by (rule MMI_adantr)
   have S4: "( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_recclt)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   from S4 S5 have S6: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_sylan)
   from S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_adantrr)
   have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   from S8 have S9: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 C \<in> \<complex>" by (rule MMI_adantr)
   from S3 S7 S9 have S10: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( A \<in> \<complex> \<and> ( \<one> \<cdiv> B ) \<in> \<complex> \<and> C \<in> \<complex> )" by (rule MMI_3jca)
   have S11: "( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_pm3_27)
   from S11 have S12: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 C \<noteq> \<zero>" by (rule MMI_adantl)
   from S1 S10 S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_sylanc)
   have S14: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrect)
   from S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_3expa)
   from S15 have S16: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_3adantl3)
   from S16 have S17: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_adantrr)
   from S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> C ) = 
 ( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdiv> C )" by (rule MMI_opreq1d)
   have S19: "( ( A \<cdiv> C ) \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<cdiv> B ) = 
 ( ( A \<cdiv> C ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrect)
   have S20: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S20 have S21: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S21 have S22: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3adantl2)
   from S22 have S23: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_adantrl)
   from S5 have S24: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" .
   from S24 have S25: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 B \<in> \<complex>" by (rule MMI_adantr)
   have S26: "( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_pm3_26)
   from S26 have S27: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 B \<noteq> \<zero>" by (rule MMI_adantl)
   from S19 S23 S25 S27 have S28: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<cdiv> B ) = 
 ( ( A \<cdiv> C ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_syl3anc)
   from S13 S18 S28 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_divdiv23: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "B \<noteq> \<zero>" and
    A5: "C \<noteq> \<zero>"   
   shows "( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A4 have S3: "B \<noteq> \<zero>".
   from S2 S3 have S4: "( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_reccl)
   from A3 have S5: "C \<in> \<complex>".
   from A5 have S6: "C \<noteq> \<zero>".
   from S1 S4 S5 S6 have S7: "( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_div23)
   from A1 have S8: "A \<in> \<complex>".
   from A2 have S9: "B \<in> \<complex>".
   from A4 have S10: "B \<noteq> \<zero>".
   from S8 S9 S10 have S11: "( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrec)
   from S11 have S12: "( ( A \<cdiv> B ) \<cdiv> C ) = 
 ( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdiv> C )" by (rule MMI_opreq1i)
   from A1 have S13: "A \<in> \<complex>".
   from A3 have S14: "C \<in> \<complex>".
   from A5 have S15: "C \<noteq> \<zero>".
   from S13 S14 S15 have S16: "( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divcl)
   from A2 have S17: "B \<in> \<complex>".
   from A4 have S18: "B \<noteq> \<zero>".
   from S16 S17 S18 have S19: "( ( A \<cdiv> C ) \<cdiv> B ) = 
 ( ( A \<cdiv> C ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrec)
   from S7 S12 S19 show "( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_divdiv23z: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   from S1 S2 S3 have S4: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex>" by (rule MMI_3pm3_2i)
   have S5: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )" by (rule MMI_divdiv23t)
   from S4 S5 show "( B \<noteq> \<zero> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdiv> B )" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_redivcl: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "B \<noteq> \<zero>"   
   shows "( A \<cdiv> B ) \<in> \<real>"
proof -
   from A1 have S1: "A \<in> \<real>".
   from S1 have S2: "A \<in> \<complex>" by (rule MMI_recn)
   from A2 have S3: "B \<in> \<real>".
   from S3 have S4: "B \<in> \<complex>" by (rule MMI_recn)
   from A3 have S5: "B \<noteq> \<zero>".
   from S2 S4 S5 have S6: "( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrec)
   from A1 have S7: "A \<in> \<real>".
   from A2 have S8: "B \<in> \<real>".
   from A3 have S9: "B \<noteq> \<zero>".
   have S10: "( B \<in> \<real> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<exists> x \<in> \<real> . ( B \<cdot> x ) = \<one> )" by (rule MMI_axrrecex)
   from S8 S9 S10 have S11: "\<exists> x \<in> \<real> . ( B \<cdot> x ) = \<one>" by (rule MMI_mp2an)
   have S12: "( \<exists> x \<in> \<real> . ( B \<cdot> x ) = 
 \<one> ) \<longleftrightarrow> 
 ( \<exists> x . ( x \<in> \<real> \<and> ( B \<cdot> x ) = \<one> ) )" by (rule MMI_df_rex)
   { fix x
     have S13: "x \<in> \<real> \<longrightarrow> x \<in> \<complex>" by (rule MMI_recnt)
     have S14: "x = if ( x \<in> \<complex> , x , \<one> ) \<longrightarrow>  ( ( \<one> \<cdiv> B ) =  x \<longleftrightarrow> 
       ( \<one> \<cdiv> B ) = if ( x \<in> \<complex> , x , \<one> ) )" by (rule MMI_eqeq2)
     have S15: "x = if ( x \<in> \<complex> , x , \<one> ) \<longrightarrow>  
       ( B \<cdot> x ) = ( B \<cdot> if ( x \<in> \<complex> , x , \<one> ) )" by (rule MMI_opreq2)
     from S15 have S16: "x = if ( x \<in> \<complex> , x , \<one> ) \<longrightarrow> 
       ( ( B \<cdot> x ) =  \<one> \<longleftrightarrow> ( B \<cdot> if ( x \<in> \<complex> , x , \<one> ) ) = \<one> )" by (rule MMI_eqeq1d)
     from S14 S16 have S17: "x =  if ( x \<in> \<complex> , x , \<one> ) \<longrightarrow> 
       ( ( ( \<one> \<cdiv> B ) = x \<longleftrightarrow> ( B \<cdot> x ) = \<one> ) \<longleftrightarrow> 
       ( ( \<one> \<cdiv> B ) = if ( x \<in> \<complex> , x , \<one> ) \<longleftrightarrow> 
       ( B \<cdot> if ( x \<in> \<complex> , x , \<one> ) ) = \<one> ) )" by (rule MMI_bibi12d)
     have S18: "\<one> \<in> \<complex>" by (rule MMI_1cn)
     from S4 have S19: "B \<in> \<complex>" .
     have S20: "\<one> \<in> \<complex>" by (rule MMI_1cn)
     from S20 have S21: "if ( x \<in> \<complex> , x , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
     from A3 have S22: "B \<noteq> \<zero>".
     from S18 S19 S21 S22 have S23: "( \<one> \<cdiv> B ) = 
       if ( x \<in> \<complex> , x , \<one> ) \<longleftrightarrow> 
       ( B \<cdot> if ( x \<in> \<complex> , x , \<one> ) ) = \<one>" by (rule MMI_divmul)
     from S17 S23 have S24: "x \<in> \<complex> \<longrightarrow> 
       ( ( \<one> \<cdiv> B ) = x \<longleftrightarrow> ( B \<cdot> x ) = \<one> )" by (rule MMI_dedth)
     from S13 S24 have S25: "x \<in> \<real> \<longrightarrow> 
       ( ( \<one> \<cdiv> B ) = x \<longleftrightarrow> ( B \<cdot> x ) = \<one> )" by (rule MMI_syl)
     have S26: "x \<in> \<real> \<longrightarrow> 
       ( ( \<one> \<cdiv> B ) = x \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<real> )" by (rule MMI_eleq1a)
     from S25 S26 have S27: "x \<in> \<real> \<longrightarrow> 
       ( ( B \<cdot> x ) = \<one> \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<real> )" by (rule MMI_sylbird)
     from S27 have  "( x \<in> \<real> \<and> ( B \<cdot> x ) = 
       \<one> ) \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<real>" by (rule MMI_imp)
   } then have S28: 
       "\<forall>x. ( x \<in> \<real> \<and> ( B \<cdot> x ) = \<one> ) \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<real>"
     by auto
     from S28 have S29: "( \<exists> x . ( x \<in> \<real> \<and> ( B \<cdot> x ) = \<one> ) ) \<longrightarrow> 
       ( \<one> \<cdiv> B ) \<in> \<real>" by (rule MMI_19_23aiv)
   from S12 S29 have S30: "( \<exists> x \<in> \<real> . ( B \<cdot> x ) = 
 \<one> ) \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<real>" by (rule MMI_sylbi)
   from S11 S30 have S31: "( \<one> \<cdiv> B ) \<in> \<real>" by (rule MMI_ax_mp)
   from S7 S31 have S32: "( A \<cdot> ( \<one> \<cdiv> B ) ) \<in> \<real>" by (rule MMI_remulcl)
   from S6 S32 show "( A \<cdiv> B ) \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_redivclz: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<real>"
proof -
   have S1: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_opreq2)
   from S1 have S2: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<in> \<real> \<longleftrightarrow> 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) \<in> \<real> )" by (rule MMI_eleq1d)
   from A1 have S3: "A \<in> \<real>".
   from A2 have S4: "B \<in> \<real>".
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S4 S5 have S6: "if ( B \<noteq> \<zero> , B , \<one> ) \<in> \<real>" by (rule MMI_keepel)
   have S7: "if ( B \<noteq> \<zero> , B , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S3 S6 S7 have S8: "( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) \<in> \<real>" by (rule MMI_redivcl)
   from S2 S8 show "B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<real>" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_redivclt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<real>"
proof -
   have S1: "A = 
 if ( A \<in> \<real> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<real> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<in> \<real> \<longleftrightarrow> 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> B ) \<in> \<real> )" by (rule MMI_eleq1d)
   from S2 have S3: "A = 
 if ( A \<in> \<real> , A , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<real> ) \<longleftrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> B ) \<in> \<real> ) )" by (rule MMI_imbi2d)
   have S4: "B = 
 if ( B \<in> \<real> , B , \<zero> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longleftrightarrow> if ( B \<in> \<real> , B , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S5: "B = 
 if ( B \<in> \<real> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> if ( B \<in> \<real> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S5 have S6: "B = 
 if ( B \<in> \<real> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> B ) \<in> \<real> \<longleftrightarrow> 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> if ( B \<in> \<real> , B , \<zero> ) ) \<in> \<real> )" by (rule MMI_eleq1d)
   from S4 S6 have S7: "B = 
 if ( B \<in> \<real> , B , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> B ) \<in> \<real> ) \<longleftrightarrow> 
 ( if ( B \<in> \<real> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> if ( B \<in> \<real> , B , \<zero> ) ) \<in> \<real> ) )" by (rule MMI_imbi12d)
   have S8: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S8 have S9: "if ( A \<in> \<real> , A , \<zero> ) \<in> \<real>" by (rule MMI_elimel)
   have S10: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S10 have S11: "if ( B \<in> \<real> , B , \<zero> ) \<in> \<real>" by (rule MMI_elimel)
   from S9 S11 have S12: "if ( B \<in> \<real> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<real> , A , \<zero> ) \<cdiv> if ( B \<in> \<real> , B , \<zero> ) ) \<in> \<real>" by (rule MMI_redivclz)
   from S3 S7 S12 have S13: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<real> )" by (rule MMI_dedth2h)
   from S13 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<real>" by (rule MMI_3impia)
qed

(*********221-223*******************************************)

lemma (in MMIsar0) MMI_rereccl: assumes A1: "A \<in> \<real>" and
    A2: "A \<noteq> \<zero>"   
   shows "( \<one> \<cdiv> A ) \<in> \<real>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from A1 have S2: "A \<in> \<real>".
   from A2 have S3: "A \<noteq> \<zero>".
   from S1 S2 S3 show "( \<one> \<cdiv> A ) \<in> \<real>" by (rule MMI_redivcl)
qed

lemma (in MMIsar0) MMI_rerecclz: assumes A1: "A \<in> \<real>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<real>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 show "A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<real>" by (rule MMI_redivclz)
qed

lemma (in MMIsar0) MMI_rerecclt: 
   shows "( A \<in> \<real> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<real>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "( \<one> \<in> \<real> \<and> A \<in> \<real> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) \<in> \<real>" by (rule MMI_redivclt)
   from S1 S2 show "( A \<in> \<real> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<real>" 
     by (rule MMI_mp3an1)
qed

(*********** a couple of definitions translated by hand ****)

lemma (in MMIsar0) MMI_df_pnf: shows "\<cpnf> = \<complex>"
  using cpnf_def by simp

lemma (in MMIsar0) MMI_df_mnf: shows "\<cmnf> = {\<complex>}"
  using cmnf_def by simp

lemma (in MMIsar0) MMI_df_xr: shows "\<real>\<^sup>* = \<real> \<union> {\<cpnf>,\<cmnf>}"
  using cxr_def by simp

lemma (in MMIsar0) MMI_ltxrt: shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
  ( A \<ls> B \<longleftrightarrow>   
  ( ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<or> 
  ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )"
  using cxr_def lessr_def cxr_def cltrrset_def cltrr_def by auto

(***223-225***************************************)

lemma (in MMIsar0) MMI_pnfnre: 
   shows "\<cpnf> \<notin> \<real>"
proof -
   have S1: "\<not> ( \<complex> \<in> \<complex> )" by (rule MMI_eirr)
   have S2: "\<cpnf> = \<complex>" by (rule MMI_df_pnf)
   from S2 have S3: "\<cpnf> \<in> \<complex> \<longleftrightarrow> \<complex> \<in> \<complex>" by (rule MMI_eleq1i)
   from S1 S3 have S4: "\<not> ( \<cpnf> \<in> \<complex> )" by (rule MMI_mtbir)
   have S5: "\<cpnf> \<in> \<real> \<longrightarrow> \<cpnf> \<in> \<complex>" by (rule MMI_recnt)
   from S4 S5 have S6: "\<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_mto)
   have S7: "\<cpnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S6 S7 show "\<cpnf> \<notin> \<real>" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_minfnre: 
   shows "\<cmnf> \<notin> \<real>"
proof -
   have S1: "\<complex> isASet" by (rule MMI_axcnex)
   from S1 have S2: "\<complex> \<in> { \<complex> }" by (rule MMI_snid)
   have S3: "\<not> ( ( \<complex> \<in> { \<complex> } \<and> { \<complex> } \<in> \<complex> ) )" by (rule MMI_en2lp)
   have S4: "( \<complex> \<in> { \<complex> } \<longrightarrow> 
 \<not> ( { \<complex> } \<in> \<complex> ) ) \<longleftrightarrow> 
 \<not> ( ( \<complex> \<in> { \<complex> } \<and> { \<complex> } \<in> \<complex> ) )" by (rule MMI_imnan)
   from S3 S4 have S5: "\<complex> \<in> { \<complex> } \<longrightarrow> \<not> ( { \<complex> } \<in> \<complex> )" by (rule MMI_mpbir)
   from S2 S5 have S6: "\<not> ( { \<complex> } \<in> \<complex> )" by (rule MMI_ax_mp)
   have S7: "\<cmnf> = { \<complex> }" by (rule MMI_df_mnf)
   from S7 have S8: "\<cmnf> \<in> \<complex> \<longleftrightarrow> { \<complex> } \<in> \<complex>" by (rule MMI_eleq1i)
   from S6 S8 have S9: "\<not> ( \<cmnf> \<in> \<complex> )" by (rule MMI_mtbir)
   have S10: "\<cmnf> \<in> \<real> \<longrightarrow> \<cmnf> \<in> \<complex>" by (rule MMI_recnt)
   from S9 S10 have S11: "\<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_mto)
   have S12: "\<cmnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S11 S12 show "\<cmnf> \<notin> \<real>" by (rule MMI_mpbir)
qed

(***********226-228*********************************)

lemma (in MMIsar0) MMI_ressxr: 
   shows "\<real> \<subseteq> \<real>\<^sup>*"
proof -
   have S1: "\<real> \<subseteq> ( \<real> \<union> { \<cpnf> , \<cmnf> } )" by (rule MMI_ssun1)
   have S2: "\<real>\<^sup>* = ( \<real> \<union> { \<cpnf> , \<cmnf> } )" by (rule MMI_df_xr)
   from S1 S2 show "\<real> \<subseteq> \<real>\<^sup>*" by (rule MMI_sseqtr4)
qed

lemma (in MMIsar0) MMI_rexrt: 
   shows "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*"
proof -
   have S1: "\<real> \<subseteq> \<real>\<^sup>*" by (rule MMI_ressxr)
   from S1 show "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_sseli)
qed

lemma (in MMIsar0) MMI_ltxrltt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<lsr> B )"
proof -
   have S1: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
     ( A \<ls> B \<longleftrightarrow>   
     ( ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<or> 
     ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   from S1 S2 S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<or> 
     ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )" by (rule MMI_syl2an)
   have S5: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsr> B \<longleftrightarrow>   
 ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) )" by (rule MMI_ibar)
   have S6: "\<cpnf> \<notin> \<real>" by (rule MMI_pnfnre)
   have S7: "\<cpnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S6 S7 have S8: "\<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_mpbi)
   have S9: "B = \<cpnf> \<longrightarrow> ( B \<in> \<real> \<longleftrightarrow> \<cpnf> \<in> \<real> )" by (rule MMI_eleq1)
   from S8 S9 have S10: "B = \<cpnf> \<longrightarrow> \<not> ( B \<in> \<real> )" by (rule MMI_mtbiri)
   from S10 have S11: "B \<in> \<real> \<longrightarrow> \<not> ( B = \<cpnf> )" by (rule MMI_con2i)
   from S11 have S12: "B \<in> \<real> \<longrightarrow> \<not> ( ( A = \<cmnf> \<and> B = \<cpnf> ) )" by (rule MMI_intnand)
   from S12 have S13: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 \<not> ( ( A = \<cmnf> \<and> B = \<cpnf> ) )" by (rule MMI_adantl)
   from S11 have S14: "B \<in> \<real> \<longrightarrow> \<not> ( B = \<cpnf> )" .
   from S14 have S15: "B \<in> \<real> \<longrightarrow> \<not> ( ( A \<in> \<real> \<and> B = \<cpnf> ) )" by (rule MMI_intnand)
   have S16: "\<cmnf> \<notin> \<real>" by (rule MMI_minfnre)
   have S17: "\<cmnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S16 S17 have S18: "\<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_mpbi)
   have S19: "A = \<cmnf> \<longrightarrow> ( A \<in> \<real> \<longleftrightarrow> \<cmnf> \<in> \<real> )" by (rule MMI_eleq1)
   from S18 S19 have S20: "A = \<cmnf> \<longrightarrow> \<not> ( A \<in> \<real> )" by (rule MMI_mtbiri)
   from S20 have S21: "A \<in> \<real> \<longrightarrow> \<not> ( A = \<cmnf> )" by (rule MMI_con2i)
   from S21 have S22: "A \<in> \<real> \<longrightarrow> \<not> ( ( A = \<cmnf> \<and> B \<in> \<real> ) )" by (rule MMI_intnanrd)
   from S15 S22 have S23: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( ( A \<in> \<real> \<and> B = \<cpnf> ) ) \<and> \<not> ( ( A = \<cmnf> \<and> B \<in> \<real> ) ) )" by (rule MMI_anim12i)
   have S24: "\<not> ( ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<longleftrightarrow>   
 ( \<not> ( ( A \<in> \<real> \<and> B = \<cpnf> ) ) \<and> \<not> ( ( A = \<cmnf> \<and> B \<in> \<real> ) ) )" by (rule MMI_ioran)
   from S23 S24 have S25: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 \<not> ( ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) )" by (rule MMI_sylibr)
   from S25 have S26: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 \<not> ( ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) )" by (rule MMI_ancoms)
   from S13 S26 have S27: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<and> \<not> ( ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )" by (rule MMI_jca)
   have S28: "\<not> ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) ) \<longleftrightarrow>   
 ( \<not> ( ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<and> \<not> ( ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )" by (rule MMI_ioran)
   from S27 S28 have S29: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 \<not> ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )" by (rule MMI_sylibr)
   have S30: "\<not> ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) ) \<longrightarrow>   
 ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<longleftrightarrow>   
 ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<or> ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) ) )" 
     by (rule MMI_biorf)
   from S29 S30 have S31: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<longleftrightarrow>   
 ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<or> ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) ) )" 
     by (rule MMI_syl)
   from S5 S31 have S32: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<or> ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) ) \<longleftrightarrow>   
 A \<lsr> B )" by (rule MMI_bitr2d)
   have S33: "( ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> 
     ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<longleftrightarrow>   
 ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> 
     ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) )" by (rule MMI_orass)
   have S34: "( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> 
     ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) ) \<longleftrightarrow>   
 ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<or> ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) )" 
     by (rule MMI_orcom)
   from S33 S34 have S35: "( ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> 
     ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<longleftrightarrow>   
 ( ( ( A = \<cmnf> \<and> B = \<cpnf> ) \<or> ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> 
     ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<or> ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) )" 
     by (rule MMI_bitr)
   from S32 S35 have S36: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( ( ( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsr> B ) \<or> ( A = \<cmnf> \<and> B = \<cpnf> ) ) \<or> 
     ( ( A \<in> \<real> \<and> B = \<cpnf> ) \<or> ( A = \<cmnf> \<and> B \<in> \<real> ) ) ) \<longleftrightarrow>   
 A \<lsr> B )" by (rule MMI_syl5bb)
   from S4 S36 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<lsr> B )" 
     by (rule MMI_bitrd)
qed

(*********** proven by hand from definition********
    note that MMIsar definition of \<lsq> (see the locale
    (is different than Metamath's, we may have to change it 
    if it leads problems.
    ******************************************************)

lemma (in MMIsar0) MMI_xrlenltt: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
  ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )"
  using lsq_def by simp


(*********229,230*******************************)

lemma (in MMIsar0) MMI_axlttri: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<ls> A ) ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsr> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<lsr> A ) ) )" by (rule MMI_pre_axlttri)
   have S2: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<lsr> B )" by (rule MMI_ltxrltt)
   have S3: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> B \<lsr> A )" by (rule MMI_ltxrltt)
   from S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> B \<lsr> A )" by (rule MMI_ancoms)
   from S4 have S5: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( A = B \<or> B \<ls> A ) \<longleftrightarrow>   
 ( A = B \<or> B \<lsr> A ) )" by (rule MMI_orbi2d)
   from S5 have S6: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( ( A = B \<or> B \<ls> A ) ) \<longleftrightarrow>   
 \<not> ( ( A = B \<or> B \<lsr> A ) ) )" by (rule MMI_negbid)
   from S1 S2 S6 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<ls> A ) ) )" by (rule MMI_3bitr4d)
qed

lemma (in MMIsar0) MMI_axlttrn: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsr> B \<and> B \<lsr> C ) \<longrightarrow> A \<lsr> C )" by (rule MMI_pre_axlttrn)
   have S2: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<lsr> B )" by (rule MMI_ltxrltt)
   from S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> A \<lsr> B )" by (rule MMI_3adant3)
   have S4: "( B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow> ( B \<ls> C \<longleftrightarrow> B \<lsr> C )" by (rule MMI_ltxrltt)
   from S4 have S5: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<ls> C \<longleftrightarrow> B \<lsr> C )" by (rule MMI_3adant1)
   from S3 S5 have S6: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longleftrightarrow>   
 ( A \<lsr> B \<and> B \<lsr> C ) )" by (rule MMI_anbi12d)
   have S7: "( A \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow> ( A \<ls> C \<longleftrightarrow> A \<lsr> C )" by (rule MMI_ltxrltt)
   from S7 have S8: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> C \<longleftrightarrow> A \<lsr> C )" by (rule MMI_3adant2)
   from S1 S6 S8 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3imtr4d)
qed

(***************231-235********************************)

lemma (in MMIsar0) MMI_axltadd: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( C \<ca> A ) \<ls> ( C \<ca> B ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<lsr> B \<longrightarrow> ( C \<ca> A ) \<lsr> ( C \<ca> B ) )" by (rule MMI_pre_axltadd)
   have S2: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<lsr> B )" by (rule MMI_ltxrltt)
   from S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> A \<lsr> B )" by (rule MMI_3adant3)
   have S4: "( ( C \<ca> A ) \<in> \<real> \<and> ( C \<ca> B ) \<in> \<real> ) \<longrightarrow>   
 ( ( C \<ca> A ) \<ls> ( C \<ca> B ) \<longleftrightarrow>   
 ( C \<ca> A ) \<lsr> ( C \<ca> B ) )" by (rule MMI_ltxrltt)
   have S5: "( C \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow> ( C \<ca> A ) \<in> \<real>" by (rule MMI_axaddrcl)
   have S6: "( C \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( C \<ca> B ) \<in> \<real>" by (rule MMI_axaddrcl)
   from S4 S5 S6 have S7: "( ( C \<in> \<real> \<and> A \<in> \<real> ) \<and> ( C \<in> \<real> \<and> B \<in> \<real> ) ) \<longrightarrow>   
 ( ( C \<ca> A ) \<ls> ( C \<ca> B ) \<longleftrightarrow>   
 ( C \<ca> A ) \<lsr> ( C \<ca> B ) )" by (rule MMI_syl2an)
   from S7 have S8: "( C \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( C \<ca> A ) \<ls> ( C \<ca> B ) \<longleftrightarrow>   
 ( C \<ca> A ) \<lsr> ( C \<ca> B ) )" by (rule MMI_3impdi)
   from S8 have S9: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( C \<ca> A ) \<ls> ( C \<ca> B ) \<longleftrightarrow>   
 ( C \<ca> A ) \<lsr> ( C \<ca> B ) )" by (rule MMI_3coml)
   from S1 S3 S9 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( C \<ca> A ) \<ls> ( C \<ca> B ) )" by (rule MMI_3imtr4d)
qed

lemma (in MMIsar0) MMI_axmulgt0: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( \<zero> \<ls> A \<and> \<zero> \<ls> B ) \<longrightarrow> \<zero> \<ls> ( A \<cdot> B ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( \<zero> \<lsr> A \<and> \<zero> \<lsr> B ) \<longrightarrow> \<zero> \<lsr> ( A \<cdot> B ) )" by (rule MMI_pre_axmulgt0)
   have S2: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S3: "( \<zero> \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow> ( \<zero> \<ls> A \<longleftrightarrow> \<zero> \<lsr> A )" by (rule MMI_ltxrltt)
   from S2 S3 have S4: "A \<in> \<real> \<longrightarrow> ( \<zero> \<ls> A \<longleftrightarrow> \<zero> \<lsr> A )" by (rule MMI_mpan)
   have S5: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S6: "( \<zero> \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( \<zero> \<ls> B \<longleftrightarrow> \<zero> \<lsr> B )" by (rule MMI_ltxrltt)
   from S5 S6 have S7: "B \<in> \<real> \<longrightarrow> ( \<zero> \<ls> B \<longleftrightarrow> \<zero> \<lsr> B )" by (rule MMI_mpan)
   from S4 S7 have S8: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( \<zero> \<ls> A \<and> \<zero> \<ls> B ) \<longleftrightarrow>   
 ( \<zero> \<lsr> A \<and> \<zero> \<lsr> B ) )" by (rule MMI_bi2anan9)
   have S9: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<real>" by (rule MMI_axmulrcl)
   have S10: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S11: "( \<zero> \<in> \<real> \<and> ( A \<cdot> B ) \<in> \<real> ) \<longrightarrow>   
 ( \<zero> \<ls> ( A \<cdot> B ) \<longleftrightarrow> \<zero> \<lsr> ( A \<cdot> B ) )" by (rule MMI_ltxrltt)
   from S10 S11 have S12: "( A \<cdot> B ) \<in> \<real> \<longrightarrow>   
 ( \<zero> \<ls> ( A \<cdot> B ) \<longleftrightarrow> \<zero> \<lsr> ( A \<cdot> B ) )" by (rule MMI_mpan)
   from S9 S12 have S13: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<zero> \<ls> ( A \<cdot> B ) \<longleftrightarrow> \<zero> \<lsr> ( A \<cdot> B ) )" by (rule MMI_syl)
   from S1 S8 S13 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( \<zero> \<ls> A \<and> \<zero> \<ls> B ) \<longrightarrow> \<zero> \<ls> ( A \<cdot> B ) )" by (rule MMI_3imtr4d)
qed

lemma (in MMIsar0) MMI_axsup: 
   shows "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 \<and> ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<ls> x ) ) \<longrightarrow>   
 ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
  ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) ) )"
proof -
  have S1: "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 \<and> ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<lsr> x ) ) \<longrightarrow>   
    ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
    ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) )" 
    by (rule MMI_pre_axsup)
  from S1 have S2: 
    "( ( ( A \<subseteq> \<real> \<and> A \<noteq> 0 ) \<and> ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<lsr> x ) ) \<longrightarrow>   
    ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
    ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) )" 
    by (rule MMI_3expa)
  from S2 have S3: "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 ) \<longrightarrow>   
    ( ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<lsr> x ) \<longrightarrow>   
    ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
    ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) ) )" 
    by (rule MMI_ex)
  { fix x
    { fix y
      have S4: "( y \<in> \<real> \<and> x \<in> \<real> ) \<longrightarrow> ( y \<ls> x \<longleftrightarrow> y \<lsr> x )" 
	by (rule MMI_ltxrltt)
      have S5: "( ( A \<subseteq> \<real> \<and> y \<in> A ) \<longrightarrow> y \<in> \<real> )" by (rule MMI_ssel2)
      from S4 S5 have S6: "( ( ( A \<subseteq> \<real> \<and> y \<in> A ) \<and> x \<in> \<real> ) \<longrightarrow>   
	( y \<ls> x \<longleftrightarrow> y \<lsr> x ) )" by (rule MMI_sylan)
      from S6 have "( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> A ) \<longrightarrow>   
	( y \<ls> x \<longleftrightarrow> y \<lsr> x ) )" by (rule MMI_an1rs)
    } then have S7: "\<forall>y. ( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> A ) \<longrightarrow>   
	( y \<ls> x \<longleftrightarrow> y \<lsr> x ) )" by simp
    from S7 have  "( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<longrightarrow>   
      ( ( \<forall> y \<in> A . y \<ls> x ) \<longleftrightarrow>   
      ( \<forall> y \<in> A . y \<lsr> x ) ) )" by (rule MMI_ralbidva)
  } then have S8: "\<forall> x. ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<longrightarrow>   
      ( ( \<forall> y \<in> A . y \<ls> x ) \<longleftrightarrow>   
      ( \<forall> y \<in> A . y \<lsr> x ) ) )" by simp
    from S8 have S9: "( A \<subseteq> \<real> \<longrightarrow>   
      ( ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<ls> x ) \<longleftrightarrow>   
      ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<lsr> x ) ) )" by (rule MMI_rexbidva)
   from S9 have S10: "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 ) \<longrightarrow>   
 ( ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<ls> x ) \<longleftrightarrow>   
 ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<lsr> x ) ) )" by (rule MMI_adantr)
   { fix x
     { fix y 
       have S11: "( x \<in> \<real> \<and> y \<in> \<real> ) \<longrightarrow> ( x \<ls> y \<longleftrightarrow> x \<lsr> y )" by (rule MMI_ltxrltt)
       from S11 have S12: "( y \<in> \<real> \<and> x \<in> \<real> ) \<longrightarrow> ( x \<ls> y \<longleftrightarrow> x \<lsr> y )" 
	 by (rule MMI_ancoms)
       have S13: "( ( A \<subseteq> \<real> \<and> y \<in> A ) \<longrightarrow> y \<in> \<real> )" by (rule MMI_ssel2)
       from S12 S13 have S14: "( ( ( A \<subseteq> \<real> \<and> y \<in> A ) \<and> x \<in> \<real> ) \<longrightarrow>   
	 ( x \<ls> y \<longleftrightarrow> x \<lsr> y ) )" by (rule MMI_sylan)
       from S14 have S15: "( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> A ) \<longrightarrow>   
	 ( x \<ls> y \<longleftrightarrow> x \<lsr> y ) )" by (rule MMI_an1rs)
       from S15 have  "( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> A ) \<longrightarrow>   
	 ( \<not> ( x \<ls> y ) \<longleftrightarrow> \<not> ( x \<lsr> y ) ) )" by (rule MMI_negbid)
     } then have S16:  "\<forall> y. ( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> A ) \<longrightarrow>   
	 ( \<not> ( x \<ls> y ) \<longleftrightarrow> \<not> ( x \<lsr> y ) ) )" by simp
     from S16 have S17: "( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<longrightarrow>   
       ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<longleftrightarrow>   
       ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) ) )" by (rule MMI_ralbidva)
     { fix y
       have S18: "( y \<in> \<real> \<and> x \<in> \<real> ) \<longrightarrow> ( y \<ls> x \<longleftrightarrow> y \<lsr> x )" 
	 by (rule MMI_ltxrltt)
       from S18 have S19: "( x \<in> \<real> \<and> y \<in> \<real> ) \<longrightarrow> ( y \<ls> x \<longleftrightarrow> y \<lsr> x )" 
	 by (rule MMI_ancoms)
       from S19 have S20: "( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> \<real> ) \<longrightarrow>   
	 ( y \<ls> x \<longleftrightarrow> y \<lsr> x ) )" by (rule MMI_adantll)
       { fix z
	 have S21: "( y \<in> \<real> \<and> z \<in> \<real> ) \<longrightarrow> ( y \<ls> z \<longleftrightarrow> y \<lsr> z )" by (rule MMI_ltxrltt)
	 from S21 have S22: "( z \<in> \<real> \<and> y \<in> \<real> ) \<longrightarrow> ( y \<ls> z \<longleftrightarrow> y \<lsr> z )" 
	   by (rule MMI_ancoms)
	 have S23: "( ( A \<subseteq> \<real> \<and> z \<in> A ) \<longrightarrow> z \<in> \<real> )" by (rule MMI_ssel2)
	 from S22 S23 have S24: "( ( ( A \<subseteq> \<real> \<and> z \<in> A ) \<and> y \<in> \<real> ) \<longrightarrow>   
	   ( y \<ls> z \<longleftrightarrow> y \<lsr> z ) )" by (rule MMI_sylan)
	 from S24 have S25: "( ( ( A \<subseteq> \<real> \<and> y \<in> \<real> ) \<and> z \<in> A ) \<longrightarrow>   
	   ( y \<ls> z \<longleftrightarrow> y \<lsr> z ) )" by (rule MMI_an1rs)
       } then have S25: "\<forall>z. ( ( ( A \<subseteq> \<real> \<and> y \<in> \<real> ) \<and> z \<in> A ) \<longrightarrow>   
	   ( y \<ls> z \<longleftrightarrow> y \<lsr> z ) )" by simp
	 from S25 have S26: "( ( A \<subseteq> \<real> \<and> y \<in> \<real> ) \<longrightarrow>   
	 ( ( \<exists> z \<in> A . y \<ls> z ) \<longleftrightarrow>   
	 ( \<exists> z \<in> A . y \<lsr> z ) ) )" by (rule MMI_rexbidva)
	 from S26 have S27: "( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> \<real> ) \<longrightarrow>   
	   ( ( \<exists> z \<in> A . y \<ls> z ) \<longleftrightarrow>   
	   ( \<exists> z \<in> A . y \<lsr> z ) ) )" by (rule MMI_adantlr)
	 from S20 S27 have  "( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> \<real> ) \<longrightarrow>   
	   ( ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) \<longleftrightarrow>   
	   ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) )" by (rule MMI_imbi12d)
       } then have S28: "\<forall> y. ( ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<and> y \<in> \<real> ) \<longrightarrow>   
	   ( ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) \<longleftrightarrow>   
	   ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) )" by simp
       from S28 have S29: "( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<longrightarrow>   
     ( ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) \<longleftrightarrow>   
	 ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) )" 
	 by (rule MMI_ralbidva)
       from S17 S29 have  "( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<longrightarrow>   
	 ( ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
	 ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) \<longleftrightarrow>   
	 ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
	 ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) )" 
	 by (rule MMI_anbi12d)
     } then have S30: "\<forall> x. ( ( A \<subseteq> \<real> \<and> x \<in> \<real> ) \<longrightarrow>   
	 ( ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
	 ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) \<longleftrightarrow>   
	 ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
	 ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) )" 
       by simp
     from S30 have S31: "( A \<subseteq> \<real> \<longrightarrow>   
       ( ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
       ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) ) \<longleftrightarrow>   
       ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
       ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) ) )" 
       by (rule MMI_rexbidva)
     from S31 have S32: "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 ) \<longrightarrow>   
	 ( ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
       ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) ) \<longleftrightarrow>   
	 ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<lsr> y ) ) \<and> 
       ( \<forall> y \<in> \<real> . ( y \<lsr> x \<longrightarrow> ( \<exists> z \<in> A . y \<lsr> z ) ) ) ) ) ) )" 
       by (rule MMI_adantr)
       from S3 S10 S32 have S33: "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 ) \<longrightarrow>   
	 ( ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<ls> x ) \<longrightarrow>   
	 ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
	 ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) ) ) )" 
	 by (rule MMI_3imtr4d)
       from S33 show 
	 "( ( A \<subseteq> \<real> \<and> A \<noteq> 0 \<and> ( \<exists> x \<in> \<real> . \<forall> y \<in> A . y \<ls> x ) ) \<longrightarrow>   
	 ( \<exists> x \<in> \<real> . ( ( \<forall> y \<in> A . \<not> ( x \<ls> y ) ) \<and> 
	 ( \<forall> y \<in> \<real> . ( y \<ls> x \<longrightarrow> ( \<exists> z \<in> A . y \<ls> z ) ) ) ) ) )" 
	 by (rule MMI_3impia)
qed

lemma (in MMIsar0) MMI_lenltt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )"
proof -
   have S1: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_xrlenltt)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   from S1 S2 S3 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_syl2an)
qed

lemma (in MMIsar0) MMI_ltnlet: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( B \<lsq> A ) )"
proof -
   have S1: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_lenltt)
   from S1 have S2: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_ancoms)
   from S2 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( B \<lsq> A ) )" by (rule MMI_con2bid)
qed

(**********236*********************)

lemma (in MMIsar0) MMI_ltso: 
   shows "\<cltrrset> Orders \<real>"
proof -
  { fix x y z
    have S1: "( x \<in> \<real> \<and> y \<in> \<real> ) \<longrightarrow>   
      ( x \<ls> y \<longleftrightarrow> \<not> ( ( x = y \<or> y \<ls> x ) ) )" by (rule MMI_axlttri)
    from S1 have S2: "( x \<in> \<real> \<and> y \<in> \<real> \<and> z \<in> \<real> ) \<longrightarrow>   
      ( x \<ls> y \<longleftrightarrow> \<not> ( ( x = y \<or> y \<ls> x ) ) )" by (rule MMI_3adant3)
    have S3: "( x \<in> \<real> \<and> y \<in> \<real> \<and> z \<in> \<real> ) \<longrightarrow>   
      ( ( x \<ls> y \<and> y \<ls> z ) \<longrightarrow> x \<ls> z )" by (rule MMI_axlttrn)
    from S2 S3 have "( x \<in> \<real> \<and> y \<in> \<real> \<and> z \<in> \<real> ) \<longrightarrow>   
      ( ( x \<ls> y \<longleftrightarrow> \<not> ( ( x = y \<or> y \<ls> x ) ) ) \<and> 
      ( ( x \<ls> y \<and> y \<ls> z ) \<longrightarrow> x \<ls> z ) )" by (rule MMI_jca)
    then have 
      "( x \<in> \<real> \<and> y \<in> \<real> \<and> z \<in> \<real> ) \<longrightarrow>   
      ( ( \<langle>x, y\<rangle> \<in> \<cltrrset> \<longleftrightarrow> \<not> ( ( x = y \<or> \<langle>y,x\<rangle> \<in> \<cltrrset> ) ) ) \<and> 
      ( ( \<langle>x,y\<rangle> \<in> \<cltrrset> \<and> \<langle>y,z\<rangle> \<in> \<cltrrset> ) \<longrightarrow> \<langle>x, z\<rangle> \<in> \<cltrrset> ) )"
      using cltrr_def by simp
  } then have S4: "\<forall>x y z. ( x \<in> \<real> \<and> y \<in> \<real> \<and> z \<in> \<real> ) \<longrightarrow>   
      ( ( \<langle>x, y\<rangle> \<in> \<cltrrset> \<longleftrightarrow> \<not> ( ( x = y \<or> \<langle>y,x\<rangle> \<in> \<cltrrset> ) ) ) \<and> 
      ( ( \<langle>x,y\<rangle> \<in> \<cltrrset> \<and> \<langle>y,z\<rangle> \<in> \<cltrrset> ) \<longrightarrow> \<langle>x, z\<rangle> \<in> \<cltrrset> ) )"
    by auto
  from S4 show "\<cltrrset> Orders \<real>" by (rule MMI_so)
qed

(*********237-240************************)

lemma (in MMIsar0) MMI_lttri2t: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( A = B ) \<longleftrightarrow> ( A \<ls> B \<or> B \<ls> A ) )"
proof -
   have S1: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   have "( \<cltrrset> Orders \<real> \<and> ( A \<in> \<real> \<and> B \<in> \<real> ) ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> \<not> ( ( \<langle>A, B\<rangle> \<in> \<cltrrset> \<or> \<langle>B,A \<rangle> \<in> \<cltrrset>) ) )"
     by (rule MMI_sotrieq)
   then have S2: "( \<cltrrset> Orders \<real> \<and> ( A \<in> \<real> \<and> B \<in> \<real> ) ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> \<not> ( ( A \<ls> B \<or> B \<ls> A ) ) )" using cltrr_def
     by simp
   from S1 S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> \<not> ( ( A \<ls> B \<or> B \<ls> A ) ) )" by (rule MMI_mpan)
   from S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
     ( \<not> ( ( A \<ls> B \<or> B \<ls> A ) ) \<longleftrightarrow> A = B )" by (rule MMI_bicomd)
   from S4 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
     ( \<not> ( A = B ) \<longleftrightarrow> ( A \<ls> B \<or> B \<ls> A ) )" by (rule MMI_con1bid)
qed

lemma (in MMIsar0) MMI_lttri3t: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A =   
 B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )"
proof -
  have S1: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
  have "( \<cltrrset> Orders \<real> \<and> ( A \<in> \<real> \<and> B \<in> \<real> ) ) \<longrightarrow>   
    ( A = B \<longleftrightarrow> ( \<not> ( \<langle>A, B\<rangle> \<in> \<cltrrset> ) \<and> \<not> ( \<langle>B,A\<rangle> \<in> \<cltrrset> ) ) )" 
    by (rule MMI_sotrieq2)
  then have S2: "( \<cltrrset> Orders \<real> \<and> ( A \<in> \<real> \<and> B \<in> \<real> ) ) \<longrightarrow>   
    ( A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )"  using cltrr_def
    by simp
  from S1 S2 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
    ( A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_ltnet: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( A = B ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( A = B ) \<longleftrightarrow> ( A \<ls> B \<or> B \<ls> A ) )" by (rule MMI_lttri2t)
   have S2: "A \<ls> B \<longrightarrow> ( A \<ls> B \<or> B \<ls> A )" by (rule MMI_orc)
   from S1 S2 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( A = B ) )" by (rule MMI_syl5bir)
qed

lemma (in MMIsar0) MMI_letri3t: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A =   
 B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" by (rule MMI_lttri3t)
   have S2: "( \<not> ( B \<ls> A ) \<and> \<not> ( A \<ls> B ) ) \<longleftrightarrow>   
 ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) )" by (rule MMI_ancom)
   from S1 S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A =   
 B \<longleftrightarrow> ( \<not> ( B \<ls> A ) \<and> \<not> ( A \<ls> B ) ) )" by (rule MMI_syl6bbr)
   have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_lenltt)
   have S5: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_lenltt)
   from S5 have S6: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_ancoms)
   from S4 S6 have S7: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> A ) \<longleftrightarrow>   
 ( \<not> ( B \<ls> A ) \<and> \<not> ( A \<ls> B ) ) )" by (rule MMI_anbi12d)
   from S3 S7 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A ) )" by (rule MMI_bitr4d)
qed

(************** 240-250********************************)

lemma (in MMIsar0) MMI_leloet: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_lenltt)
   have S2: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( B \<ls> A \<longleftrightarrow> \<not> ( ( B = A \<or> A \<ls> B ) ) )" by (rule MMI_axlttri)
   from S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( B \<ls> A \<longleftrightarrow> \<not> ( ( B = A \<or> A \<ls> B ) ) )" by (rule MMI_ancoms)
   from S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( B = A \<or> A \<ls> B ) \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_con2bid)
   have S5: "B = A \<longleftrightarrow> A = B" by (rule MMI_eqcom)
   from S5 have S6: "( B = A \<or> A \<ls> B ) \<longleftrightarrow> ( A = B \<or> A \<ls> B )" by (rule MMI_orbi1i)
   have S7: "( A = B \<or> A \<ls> B ) \<longleftrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_orcom)
   from S6 S7 have S8: "( B = A \<or> A \<ls> B ) \<longleftrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_bitr)
   from S4 S8 have S9: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( B \<ls> A ) \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_syl5rbbr)
   from S1 S9 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_eqleltt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A \<ls> B ) ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A ) )" by (rule MMI_letri3t)
   have S2: "( B \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_lenltt)
   from S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_ancoms)
   from S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> A ) \<longleftrightarrow>   
 ( A \<lsq> B \<and> \<not> ( A \<ls> B ) ) )" by (rule MMI_anbi2d)
   from S1 S4 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A \<ls> B ) ) )" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_ltlet: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<lsq> B )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_leloet)
   have S2: "A \<ls> B \<longrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_orc)
   from S1 S2 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<lsq> B )" by (rule MMI_syl5bir)
qed

lemma (in MMIsar0) MMI_leltnet: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( A = B ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A =   
 B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" by (rule MMI_lttri3t)
   have S2: "( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) \<longrightarrow>   
 \<not> ( A \<ls> B )" by (rule MMI_pm3_26)
   from S1 S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_syl6bi)
   from S3 have S4: "( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A = B \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_adantr)
   have S5: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_leloet)
   from S5 have S6: "( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<or> A = B )" by (rule MMI_biimpa)
   from S6 have S7: "( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> A = B )" by (rule MMI_ord)
   from S4 S7 have S8: "( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_impbid)
   from S8 have S9: "( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( A = B ) )" by (rule MMI_con2bid)
   from S9 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( A = B ) )" by (rule MMI_3impa)
qed

lemma (in MMIsar0) MMI_ltlent: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A = B ) ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<lsq> B )" by (rule MMI_ltlet)
   have S2: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( A = B ) )" by (rule MMI_ltnet)
   from S1 S2 have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( A \<lsq> B \<and> \<not> ( A = B ) ) )" by (rule MMI_jcad)
   have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_leloet)
   have S5: "A \<ls> B \<longrightarrow> ( \<not> ( A = B ) \<longrightarrow> A \<ls> B )" by (rule MMI_ax_1)
   have S6: "A = B \<longrightarrow> ( \<not> ( A = B ) \<longrightarrow> A \<ls> B )" by (rule MMI_pm2_24)
   from S5 S6 have S7: "( A \<ls> B \<or> A =   
 B ) \<longrightarrow> ( \<not> ( A = B ) \<longrightarrow> A \<ls> B )" by (rule MMI_jaoi)
   from S4 S7 have S8: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( \<not> ( A = B ) \<longrightarrow> A \<ls> B ) )" by (rule MMI_syl6bi)
   from S8 have S9: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> \<not> ( A = B ) ) \<longrightarrow> A \<ls> B )" by (rule MMI_imp3a)
   from S3 S9 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A = B ) ) )" by (rule MMI_impbid)
qed

lemma (in MMIsar0) MMI_lelttrt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_leloet)
   from S1 have S2: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_3adant3)
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_axlttrn)
   from S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_exp3a)
   have S5: "A = B \<longrightarrow> ( A \<ls> C \<longleftrightarrow> B \<ls> C )" by (rule MMI_breq1)
   from S5 have S6: "A = B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C )" by (rule MMI_biimprd)
   from S6 have S7: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_a1i)
   from S4 S7 have S8: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<or> A = B ) \<longrightarrow>   
 ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_jaod)
   from S2 S8 have S9: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_sylbid)
   from S9 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_imp3a)
qed

lemma (in MMIsar0) MMI_ltletrt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<lsq> C ) \<longrightarrow> A \<ls> C )"
proof -
   have S1: "( B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_leloet)
   from S1 have S2: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_3adant1)
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_axlttrn)
   from S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_exp3a)
   from S4 have S5: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<ls> C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_com23)
   have S6: "B = C \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> C )" by (rule MMI_breq2)
   from S6 have S7: "B = C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C )" by (rule MMI_biimpd)
   from S7 have S8: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B = C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_a1i)
   from S5 S8 have S9: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( B \<ls> C \<or> B = C ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_jaod)
   from S2 S9 have S10: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_sylbid)
   from S10 have S11: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( B \<lsq> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_com23)
   from S11 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<lsq> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_imp3a)
qed

lemma (in MMIsar0) MMI_letrt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> C ) \<longrightarrow> A \<lsq> C )"
proof -
   have S1: "( B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_leloet)
   from S1 have S2: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_3adant1)
   from S2 have S3: "( ( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_adantr)
   have S4: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_lelttrt)
   have S5: "( A \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow> ( A \<ls> C \<longrightarrow> A \<lsq> C )" by (rule MMI_ltlet)
   from S5 have S6: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> C \<longrightarrow> A \<lsq> C )" by (rule MMI_3adant2)
   from S4 S6 have S7: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_syld)
   from S7 have S8: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<lsq> C ) )" by (rule MMI_exp3a)
   from S8 have S9: "( ( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B \<ls> C \<longrightarrow> A \<lsq> C )" by (rule MMI_imp)
   have S10: "B = C \<longrightarrow> ( A \<lsq> B \<longleftrightarrow> A \<lsq> C )" by (rule MMI_breq2)
   from S10 have S11: "A \<lsq> B \<longrightarrow> ( B = C \<longrightarrow> A \<lsq> C )" by (rule MMI_biimpcd)
   from S11 have S12: "( ( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B = C \<longrightarrow> A \<lsq> C )" by (rule MMI_adantl)
   from S9 S12 have S13: "( ( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( ( B \<ls> C \<or> B = C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_jaod)
   from S3 S13 have S14: "( ( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B \<lsq> C \<longrightarrow> A \<lsq> C )" by (rule MMI_sylbid)
   from S14 have S15: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( B \<lsq> C \<longrightarrow> A \<lsq> C ) )" by (rule MMI_ex)
   from S15 show "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_imp3a)
qed

lemma (in MMIsar0) MMI_letrd: assumes A1: "\<phi> \<longrightarrow> A \<in> \<real>" and
    A2: "\<phi> \<longrightarrow> B \<in> \<real>" and
    A3: "\<phi> \<longrightarrow> C \<in> \<real>" and
    A4: "\<phi> \<longrightarrow> A \<lsq> B" and
    A5: "\<phi> \<longrightarrow> B \<lsq> C"   
   shows "\<phi> \<longrightarrow> A \<lsq> C"
proof -
   from A4 have S1: "\<phi> \<longrightarrow> A \<lsq> B".
   from A5 have S2: "\<phi> \<longrightarrow> B \<lsq> C".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_letrt)
   from A1 have S4: "\<phi> \<longrightarrow> A \<in> \<real>".
   from A2 have S5: "\<phi> \<longrightarrow> B \<in> \<real>".
   from A3 have S6: "\<phi> \<longrightarrow> C \<in> \<real>".
   from S3 S4 S5 S6 have S7: "\<phi> \<longrightarrow> ( ( A \<lsq> B \<and> B \<lsq> C ) \<longrightarrow> A \<lsq> C )" 
     by (rule MMI_syl3anc)
   from S1 S2 S7 show "\<phi> \<longrightarrow> A \<lsq> C" by (rule MMI_mp2and)
qed

lemma (in MMIsar0) MMI_lelttrd: assumes A1: "\<phi> \<longrightarrow> A \<in> \<real>" and
    A2: "\<phi> \<longrightarrow> B \<in> \<real>" and
    A3: "\<phi> \<longrightarrow> C \<in> \<real>" and
    A4: "\<phi> \<longrightarrow> A \<lsq> B" and
    A5: "\<phi> \<longrightarrow> B \<ls> C"   
   shows "\<phi> \<longrightarrow> A \<ls> C"
proof -
   from A4 have S1: "\<phi> \<longrightarrow> A \<lsq> B".
   from A5 have S2: "\<phi> \<longrightarrow> B \<ls> C".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_lelttrt)
   from A1 have S4: "\<phi> \<longrightarrow> A \<in> \<real>".
   from A2 have S5: "\<phi> \<longrightarrow> B \<in> \<real>".
   from A3 have S6: "\<phi> \<longrightarrow> C \<in> \<real>".
   from S3 S4 S5 S6 have S7: "\<phi> \<longrightarrow> ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" 
     by (rule MMI_syl3anc)
   from S1 S2 S7 show "\<phi> \<longrightarrow> A \<ls> C" by (rule MMI_mp2and)
qed

(***************251-260********************************)


lemma (in MMIsar0) MMI_ltletrd: assumes A1: "\<phi> \<longrightarrow> A \<in> \<real>" and
    A2: "\<phi> \<longrightarrow> B \<in> \<real>" and
    A3: "\<phi> \<longrightarrow> C \<in> \<real>" and
    A4: "\<phi> \<longrightarrow> A \<ls> B" and
    A5: "\<phi> \<longrightarrow> B \<lsq> C"   
   shows "\<phi> \<longrightarrow> A \<ls> C"
proof -
   from A4 have S1: "\<phi> \<longrightarrow> A \<ls> B".
   from A5 have S2: "\<phi> \<longrightarrow> B \<lsq> C".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<lsq> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_ltletrt)
   from A1 have S4: "\<phi> \<longrightarrow> A \<in> \<real>".
   from A2 have S5: "\<phi> \<longrightarrow> B \<in> \<real>".
   from A3 have S6: "\<phi> \<longrightarrow> C \<in> \<real>".
   from S3 S4 S5 S6 have S7: "\<phi> \<longrightarrow> ( ( A \<ls> B \<and> B \<lsq> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_syl3anc)
   from S1 S2 S7 show "\<phi> \<longrightarrow> A \<ls> C" by (rule MMI_mp2and)
qed

lemma (in MMIsar0) MMI_lttrd: assumes A1: "\<phi> \<longrightarrow> A \<in> \<real>" and
    A2: "\<phi> \<longrightarrow> B \<in> \<real>" and
    A3: "\<phi> \<longrightarrow> C \<in> \<real>" and
    A4: "\<phi> \<longrightarrow> A \<ls> B" and
    A5: "\<phi> \<longrightarrow> B \<ls> C"   
   shows "\<phi> \<longrightarrow> A \<ls> C"
proof -
   from A4 have S1: "\<phi> \<longrightarrow> A \<ls> B".
   from A5 have S2: "\<phi> \<longrightarrow> B \<ls> C".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_axlttrn)
   from A1 have S4: "\<phi> \<longrightarrow> A \<in> \<real>".
   from A2 have S5: "\<phi> \<longrightarrow> B \<in> \<real>".
   from A3 have S6: "\<phi> \<longrightarrow> C \<in> \<real>".
   from S3 S4 S5 S6 have S7: "\<phi> \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_syl3anc)
   from S1 S2 S7 show "\<phi> \<longrightarrow> A \<ls> C" by (rule MMI_mp2and)
qed

lemma (in MMIsar0) MMI_ltnrt: 
   shows "A \<in> \<real> \<longrightarrow> \<not> ( A \<ls> A )"
proof -
   have S1: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   have "( \<cltrrset> Orders \<real> \<and> A \<in> \<real> ) \<longrightarrow> \<not> ( \<langle>A,A\<rangle> \<in> \<cltrrset> )" 
     by (rule MMI_sonr)
   then have S2: "( \<cltrrset> Orders \<real> \<and> A \<in> \<real> ) \<longrightarrow> \<not> ( A \<ls> A )" 
     using cltrr_def by simp
   from S1 S2 show "A \<in> \<real> \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_leidt: 
   shows "A \<in> \<real> \<longrightarrow> A \<lsq> A"
proof -
   have S1: "A = A" by (rule MMI_eqid)
   from S1 have S2: "\<not> ( A \<ls> A ) \<longrightarrow> A = A" by (rule MMI_a1i)
   from S2 have S3: "A \<ls> A \<or> A = A" by (rule MMI_orri)
   have S4: "( A \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> A \<longleftrightarrow> ( A \<ls> A \<or> A = A ) )" by (rule MMI_leloet)
   from S3 S4 have S5: "( A \<in> \<real> \<and> A \<in> \<real> ) \<longrightarrow> A \<lsq> A" by (rule MMI_mpbiri)
   from S5 show "A \<in> \<real> \<longrightarrow> A \<lsq> A" by (rule MMI_anidms)
qed

lemma (in MMIsar0) MMI_ltnsymt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<ls> A ) ) )" by (rule MMI_axlttri)
   have S2: "\<not> ( ( A = B \<or> B \<ls> A ) ) \<longrightarrow> \<not> ( B \<ls> A )" by (rule MMI_pm2_46)
   from S1 S2 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_syl6bi)
qed

lemma (in MMIsar0) MMI_ltnsym2t: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 \<not> ( ( A \<ls> B \<and> B \<ls> A ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_ltnsymt)
   have S2: "( A \<ls> B \<longrightarrow>   
 \<not> ( B \<ls> A ) ) \<longleftrightarrow>   
 \<not> ( ( A \<ls> B \<and> B \<ls> A ) )" by (rule MMI_imnan)
   from S1 S2 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 \<not> ( ( A \<ls> B \<and> B \<ls> A ) )" by (rule MMI_sylib)
qed

lemma (in MMIsar0) MMI_elxr: 
   shows "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )"
proof -
   have S1: "\<real>\<^sup>* = ( \<real> \<union> { \<cpnf> , \<cmnf> } )" by (rule MMI_df_xr)
   from S1 have S2: "A \<in> \<real>\<^sup>* \<longleftrightarrow> A \<in> ( \<real> \<union> { \<cpnf> , \<cmnf> } )" by (rule MMI_eleq2i)
   have S3: "A \<in> ( \<real> \<union> { \<cpnf> , \<cmnf> } ) \<longleftrightarrow>   
 ( A \<in> \<real> \<or> A \<in> { \<cpnf> , \<cmnf> } )" by (rule MMI_elun)
   have S4: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   from S4 have S5: "\<cpnf> isASet" by (rule MMI_elisseti)
   have S6: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   from S6 have S7: "\<cmnf> isASet" by (rule MMI_elisseti)
   from S5 S7 have S8: "A \<in> { \<cpnf> , \<cmnf> } \<longleftrightarrow> ( A = \<cpnf> \<or> A = \<cmnf> )"
     by (rule MMI_elpr2)
   from S8 have S9: "( A \<in> \<real> \<or> A \<in> { \<cpnf> , \<cmnf> } ) \<longleftrightarrow>   
 ( A \<in> \<real> \<or> ( A = \<cpnf> \<or> A = \<cmnf> ) )" by (rule MMI_orbi2i)
   have S10: "( A \<in> \<real> \<or> A =   
 \<cpnf> \<or> A =   
 \<cmnf> ) \<longleftrightarrow> ( A \<in> \<real> \<or> ( A = \<cpnf> \<or> A = \<cmnf> ) )" by (rule MMI_3orass)
   from S9 S10 have S11: "( A \<in> \<real> \<or> A \<in> { \<cpnf> , \<cmnf> } ) \<longleftrightarrow>   
 ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" by (rule MMI_bitr4)
   from S2 S3 S11 show "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" 
     by (rule MMI_3bitr)
qed

lemma (in MMIsar0) MMI_pnfnemnf: 
   shows "\<cpnf> \<noteq> \<cmnf>"
proof -
   have S1: "\<not> ( \<complex> \<in> \<complex> )" by (rule MMI_eirr)
   have S2: "\<complex> isASet" by (rule MMI_axcnex)
   from S2 have S3: "\<complex> \<in> { \<complex> }" by (rule MMI_snid)
   have S4: "\<complex> = { \<complex> } \<longrightarrow> ( \<complex> \<in> \<complex> \<longleftrightarrow> \<complex> \<in> { \<complex> } )" by (rule MMI_eleq2)
   from S3 S4 have S5: "\<complex> = { \<complex> } \<longrightarrow> \<complex> \<in> \<complex>" by (rule MMI_mpbiri)
   from S1 S5 have S6: "\<not> ( \<complex> = { \<complex> } )" by (rule MMI_mto)
   have S7: "\<cpnf> = \<complex>" by (rule MMI_df_pnf)
   have S8: "\<cmnf> = { \<complex> }" by (rule MMI_df_mnf)
   from S7 S8 have S9: "\<cpnf> = \<cmnf> \<longleftrightarrow> \<complex> = { \<complex> }" by (rule MMI_eqeq12i)
   from S6 S9 have S10: "\<not> ( \<cpnf> = \<cmnf> )" by (rule MMI_mtbir)
   have S11: "\<cpnf> \<noteq> \<cmnf> \<longleftrightarrow> \<not> ( \<cpnf> = \<cmnf> )" by (rule MMI_df_ne)
   from S10 S11 show "\<cpnf> \<noteq> \<cmnf>" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_renepnft: 
   shows "A \<in> \<real> \<longrightarrow> A \<noteq> \<cpnf>"
proof -
   have S1: "\<cpnf> \<notin> \<real>" by (rule MMI_pnfnre)
   have S2: "\<cpnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S1 S2 have S3: "\<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_mpbi)
   have S4: "( A \<in> \<real> \<and> \<not> ( \<cpnf> \<in> \<real> ) ) \<longrightarrow> \<not> ( A = \<cpnf> )" 
     by (rule MMI_nelneq)
   from S3 S4 have S5: "A \<in> \<real> \<longrightarrow> \<not> ( A = \<cpnf> )" by (rule MMI_mpan2)
   have S6: "A \<noteq> \<cpnf> \<longleftrightarrow> \<not> ( A = \<cpnf> )" by (rule MMI_df_ne)
   from S5 S6 show "A \<in> \<real> \<longrightarrow> A \<noteq> \<cpnf>" by (rule MMI_sylibr)
qed

lemma (in MMIsar0) MMI_renemnft: 
   shows "A \<in> \<real> \<longrightarrow> A \<noteq> \<cmnf>"
proof -
   have S1: "\<cmnf> \<notin> \<real>" by (rule MMI_minfnre)
   have S2: "\<cmnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S1 S2 have S3: "\<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_mpbi)
   have S4: "( A \<in> \<real> \<and> \<not> ( \<cmnf> \<in> \<real> ) ) \<longrightarrow> \<not> ( A = \<cmnf> )" 
     by (rule MMI_nelneq)
   from S3 S4 have S5: "A \<in> \<real> \<longrightarrow> \<not> ( A = \<cmnf> )" by (rule MMI_mpan2)
   have S6: "A \<noteq> \<cmnf> \<longleftrightarrow> \<not> ( A = \<cmnf> )" by (rule MMI_df_ne)
   from S5 S6 show "A \<in> \<real> \<longrightarrow> A \<noteq> \<cmnf>" by (rule MMI_sylibr)
qed

(**********************261-270***********************)

lemma (in MMIsar0) MMI_renfdisj: 
   shows "( \<real> \<inter> { \<cpnf> , \<cmnf> } ) = 0"
proof -
   have S1: "{ \<cpnf> , \<cmnf> } = ( { \<cpnf> } \<union> { \<cmnf> } )" by (rule MMI_df_pr)
   from S1 have S2: "( \<real> \<inter> { \<cpnf> , \<cmnf> } ) =   
 ( \<real> \<inter> ( { \<cpnf> } \<union> { \<cmnf> } ) )" by (rule MMI_ineq2i)
   have S3: "\<cpnf> = \<cpnf>" by (rule MMI_eqid)
   have S4: "\<cpnf> \<in> \<real> \<longrightarrow> \<cpnf> \<noteq> \<cpnf>" by (rule MMI_renepnft)
   have S5: "\<cpnf> \<noteq> \<cpnf> \<longleftrightarrow> \<not> ( \<cpnf> = \<cpnf> )" by (rule MMI_df_ne)
   from S4 S5 have S6: "\<cpnf> \<in> \<real> \<longrightarrow> \<not> ( \<cpnf> = \<cpnf> )" by (rule MMI_sylib)
   from S3 S6 have S7: "\<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_mt2)
   have S8: "( \<real> \<inter> { \<cpnf> } ) = 0 \<longleftrightarrow> \<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_disjsn)
   from S7 S8 have S9: "( \<real> \<inter> { \<cpnf> } ) = 0" by (rule MMI_mpbir)
   have S10: "\<cmnf> = \<cmnf>" by (rule MMI_eqid)
   have S11: "\<cmnf> \<in> \<real> \<longrightarrow> \<cmnf> \<noteq> \<cmnf>" by (rule MMI_renemnft)
   have S12: "\<cmnf> \<noteq> \<cmnf> \<longleftrightarrow> \<not> ( \<cmnf> = \<cmnf> )" by (rule MMI_df_ne)
   from S11 S12 have S13: "\<cmnf> \<in> \<real> \<longrightarrow> \<not> ( \<cmnf> = \<cmnf> )" by (rule MMI_sylib)
   from S10 S13 have S14: "\<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_mt2)
   have S15: "( \<real> \<inter> { \<cmnf> } ) = 0 \<longleftrightarrow> \<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_disjsn)
   from S14 S15 have S16: "( \<real> \<inter> { \<cmnf> } ) = 0" by (rule MMI_mpbir)
   from S9 S16 have S17: "( \<real> \<inter> { \<cpnf> } ) = 0 \<and> ( \<real> \<inter> { \<cmnf> } ) = 0" by (rule MMI_pm3_2i)
   have S18: "( ( \<real> \<inter> { \<cpnf> } ) =   
 0 \<and> ( \<real> \<inter> { \<cmnf> } ) =   
 0 ) \<longleftrightarrow> ( \<real> \<inter> ( { \<cpnf> } \<union> { \<cmnf> } ) ) = 0" by (rule MMI_undisj2)
   from S17 S18 have S19: "( \<real> \<inter> ( { \<cpnf> } \<union> { \<cmnf> } ) ) = 0" by (rule MMI_mpbi)
   from S2 S19 show "( \<real> \<inter> { \<cpnf> , \<cmnf> } ) = 0" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_ssxr: 
   shows "( A \<subseteq> \<real>\<^sup>* \<longrightarrow> ( A \<subseteq> \<real> \<or> \<cpnf> \<in> A \<or> \<cmnf> \<in> A ) )"
proof -
   have S1: "( ( A \<inter> { \<cpnf> , \<cmnf> } ) =   
 0 \<longrightarrow>   
 ( A \<subseteq> ( { \<cpnf> , \<cmnf> } \<union> \<real> ) \<longleftrightarrow> A \<subseteq> \<real> ) )" by (rule MMI_disjssun)
   have S2: "\<real>\<^sup>* = ( \<real> \<union> { \<cpnf> , \<cmnf> } )" by (rule MMI_df_xr)
   have S3: "( \<real> \<union> { \<cpnf> , \<cmnf> } ) = ( { \<cpnf> , \<cmnf> } \<union> \<real> )" by (rule MMI_uncom)
   from S2 S3 have S4: "\<real>\<^sup>* = ( { \<cpnf> , \<cmnf> } \<union> \<real> )" by (rule MMI_eqtr)
   from S4 have S5: "( A \<subseteq> \<real>\<^sup>* \<longleftrightarrow> A \<subseteq> ( { \<cpnf> , \<cmnf> } \<union> \<real> ) )" by (rule MMI_sseq2i)
   from S1 S5 have S6: "( ( A \<inter> { \<cpnf> , \<cmnf> } ) =   
 0 \<longrightarrow> ( A \<subseteq> \<real>\<^sup>* \<longleftrightarrow> A \<subseteq> \<real> ) )" by (rule MMI_syl5bb)
   from S6 have S7: "( A \<subseteq> \<real>\<^sup>* \<longrightarrow>   
 ( ( A \<inter> { \<cpnf> , \<cmnf> } ) = 0 \<longrightarrow> A \<subseteq> \<real> ) )" by (rule MMI_biimpcd)
   have S8: "( A \<inter> { \<cpnf> , \<cmnf> } ) =   
 0 \<longleftrightarrow> ( \<forall> x \<in> A . \<not> ( x \<in> { \<cpnf> , \<cmnf> } ) )" by (rule MMI_disj)
   from S7 S8 have S9: "( A \<subseteq> \<real>\<^sup>* \<longrightarrow>   
 ( ( \<forall> x \<in> A . \<not> ( x \<in> { \<cpnf> , \<cmnf> } ) ) \<longrightarrow>   
 A \<subseteq> \<real> ) )" by (rule MMI_syl5ibr)
   from S9 have S10: "( A \<subseteq> \<real>\<^sup>* \<longrightarrow>   
 ( \<not> ( A \<subseteq> \<real> ) \<longrightarrow>   
 \<not> ( ( \<forall> x \<in> A . \<not> ( x \<in> { \<cpnf> , \<cmnf> } ) ) ) ) )" by (rule MMI_con3d)
   have S11: "( \<exists> x \<in> A . x \<in> { \<cpnf> , \<cmnf> } ) \<longleftrightarrow>   
     \<not> ( ( \<forall> x \<in> A . \<not> ( x \<in> { \<cpnf> , \<cmnf> } ) ) )" by (rule MMI_dfrex2)
   { fix x
     have S12: "x isASet" by (rule MMI_visset)
     from S12 have 
       "x \<in> { \<cpnf> , \<cmnf> } \<longleftrightarrow> ( x = \<cpnf> \<or> x = \<cmnf> )" 
       by (rule MMI_elpr)
   } then have S13: 
       "\<forall>x. x \<in> { \<cpnf> , \<cmnf> } \<longleftrightarrow> ( x = \<cpnf> \<or> x = \<cmnf> )"  
     by simp
   from S13 have S14: "( \<exists> x \<in> A . x \<in> { \<cpnf> , \<cmnf> } ) \<longleftrightarrow>   
     ( \<exists> x \<in> A . ( x = \<cpnf> \<or> x = \<cmnf> ) )" by (rule MMI_rexbii)
   from S11 S14 have S15: 
     "\<not> ( ( \<forall> x \<in> A . \<not> ( x \<in> { \<cpnf> , \<cmnf> } ) ) ) \<longleftrightarrow>   
     ( \<exists> x \<in> A . ( x = \<cpnf> \<or> x = \<cmnf> ) )" by (rule MMI_bitr3)
   have S16: "( \<exists> x \<in> A . ( x = \<cpnf> \<or> x = \<cmnf> ) ) \<longleftrightarrow>   
 ( ( \<exists> x \<in> A . x = \<cpnf> \<or> ( \<exists> x \<in> A . x = \<cmnf> ) ) )" 
     by (rule MMI_r19_43)
   have S17: "( \<exists> x \<in> A . x =   
 \<cpnf> ) \<longleftrightarrow> ( \<exists> x . ( x \<in> A \<and> x = \<cpnf> ) )" by (rule MMI_df_rex)
   have S18: "( \<exists> x . ( x \<in> A \<and> x = \<cpnf> ) ) \<longleftrightarrow>   
 ( \<exists> x . ( x = \<cpnf> \<and> x \<in> A ) )" by (rule MMI_exancom)
   have S19: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   from S19 have S20: "\<cpnf> isASet" by (rule MMI_elisseti)
   { fix x
     have  "x = \<cpnf> \<longrightarrow> ( x \<in> A \<longleftrightarrow> \<cpnf> \<in> A )" by (rule MMI_eleq1)
   } then have S21: "\<forall> x. x = \<cpnf> \<longrightarrow> ( x \<in> A \<longleftrightarrow> \<cpnf> \<in> A )"
     by simp
   from S20 S21 have S22: "( \<exists> x . ( x = \<cpnf> \<and> x \<in> A ) ) \<longleftrightarrow> \<cpnf> \<in> A" 
     by (rule MMI_ceqsexv)
   from S17 S18 S22 have S23: "( \<exists> x \<in> A . x = \<cpnf> ) \<longleftrightarrow> \<cpnf> \<in> A" 
     by (rule MMI_3bitr)
   have S24: "( \<exists> x \<in> A . x =   
 \<cmnf> ) \<longleftrightarrow> ( \<exists> x . ( x \<in> A \<and> x = \<cmnf> ) )" by (rule MMI_df_rex)
   have S25: "( \<exists> x . ( x \<in> A \<and> x = \<cmnf> ) ) \<longleftrightarrow>   
 ( \<exists> x . ( x = \<cmnf> \<and> x \<in> A ) )" by (rule MMI_exancom)
   have S26: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   from S26 have S27: "\<cmnf> isASet" by (rule MMI_elisseti)
   { fix x 
     have "x = \<cmnf> \<longrightarrow> ( x \<in> A \<longleftrightarrow> \<cmnf> \<in> A )" by (rule MMI_eleq1)
   } then have S28: "\<forall>x. x = \<cmnf> \<longrightarrow> ( x \<in> A \<longleftrightarrow> \<cmnf> \<in> A )"
     by simp
   from S27 S28 have S29: "( \<exists> x . ( x = \<cmnf> \<and> x \<in> A ) ) \<longleftrightarrow> \<cmnf> \<in> A" 
     by (rule MMI_ceqsexv)
   from S24 S25 S29 have S30: "( \<exists> x \<in> A . x = \<cmnf> ) \<longleftrightarrow> \<cmnf> \<in> A" 
     by (rule MMI_3bitr)
   from S23 S30 have S31: 
     "( ( \<exists> x \<in> A . x = \<cpnf> \<or> ( \<exists> x \<in> A . x = \<cmnf> ) ) ) \<longleftrightarrow>   
     ( \<cpnf> \<in> A \<or> \<cmnf> \<in> A )" 
     by auto (* by (rule MMI_orbi12i), but I cuould'n get it to work *)
   from S15 S16 S31 have S32: 
     "\<not> ( ( \<forall> x \<in> A . \<not> ( x \<in> { \<cpnf> , \<cmnf> } ) ) ) \<longleftrightarrow>   
     ( \<cpnf> \<in> A \<or> \<cmnf> \<in> A )" by (rule MMI_3bitr)
   from S10 S32 have S33: "( A \<subseteq> \<real>\<^sup>* \<longrightarrow>   
 ( \<not> ( A \<subseteq> \<real> ) \<longrightarrow> ( \<cpnf> \<in> A \<or> \<cmnf> \<in> A ) ) )" by (rule MMI_syl6ib)
   from S33 have S34: "( A \<subseteq> \<real>\<^sup>* \<longrightarrow>   
 ( A \<subseteq> \<real> \<or> ( \<cpnf> \<in> A \<or> \<cmnf> \<in> A ) ) )" by (rule MMI_orrd)
   have S35: "( ( A \<subseteq> \<real> \<or> \<cpnf> \<in> A \<or> \<cmnf> \<in> A ) \<longleftrightarrow>   
 ( A \<subseteq> \<real> \<or> ( \<cpnf> \<in> A \<or> \<cmnf> \<in> A ) ) )" by (rule MMI_3orass)
   from S34 S35 show "( A \<subseteq> \<real>\<^sup>* \<longrightarrow> ( A \<subseteq> \<real> \<or> \<cpnf> \<in> A \<or> \<cmnf> \<in> A ) )" by (rule MMI_sylibr)
qed

lemma (in MMIsar0) MMI_xrltnrt: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> A )"
proof -
   have S1: "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" by (rule MMI_elxr)
   have S2: "A \<in> \<real> \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_ltnrt)
   have S3: "\<cpnf> \<notin> \<real>" by (rule MMI_pnfnre)
   have S4: "\<cpnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S3 S4 have S5: "\<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_mpbi)
   from S5 have S6: "\<not> ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) )" by (rule MMI_intnan)
   from S6 have S7: "\<not> ( ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cpnf> \<lsr> \<cpnf> ) )" by (rule MMI_intnanr)
   have S8: "\<cpnf> \<noteq> \<cmnf>" by (rule MMI_pnfnemnf)
   have S9: "\<cpnf> \<noteq> \<cmnf> \<longleftrightarrow> \<not> ( \<cpnf> = \<cmnf> )" by (rule MMI_df_ne)
   from S8 S9 have S10: "\<not> ( \<cpnf> = \<cmnf> )" by (rule MMI_mpbi)
   from S10 have S11: "\<not> ( ( \<cpnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) )" by (rule MMI_intnanr)
   from S7 S11 have S12: "\<not> ( ( ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cpnf> \<lsr> \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) )" by (rule MMI_pm3_2ni)
   from S5 have S13: "\<not> ( \<cpnf> \<in> \<real> )" .
   from S13 have S14: "\<not> ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) )" by (rule MMI_intnanr)
   from S5 have S15: "\<not> ( \<cpnf> \<in> \<real> )" .
   from S15 have S16: "\<not> ( ( \<cpnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) )" by (rule MMI_intnan)
   from S14 S16 have S17: "\<not> ( ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) )" by (rule MMI_pm3_2ni)
   from S12 S17 have S18: "\<not> ( ( ( ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cpnf> \<lsr> \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) ) )" by (rule MMI_pm3_2ni)
   have S19: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S20: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S21: "( \<cpnf> \<in> \<real>\<^sup>* \<and> \<cpnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cpnf> \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cpnf> \<lsr> \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S19 S20 S21 have S22: "\<cpnf> \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cpnf> \<lsr> \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cpnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) )" by (rule MMI_mp2an)
   from S18 S22 have S23: "\<not> ( \<cpnf> \<ls> \<cpnf> )" by (rule MMI_mtbir)
   have S24: "( A = \<cpnf> \<and> A = \<cpnf> ) \<longrightarrow> ( A \<ls> A \<longleftrightarrow> \<cpnf> \<ls> \<cpnf> )" by (rule MMI_breq12)
   from S24 have S25: "A = \<cpnf> \<longrightarrow> ( A \<ls> A \<longleftrightarrow> \<cpnf> \<ls> \<cpnf> )" by (rule MMI_anidms)
   from S23 S25 have S26: "A = \<cpnf> \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_mtbiri)
   have S27: "\<cmnf> \<notin> \<real>" by (rule MMI_minfnre)
   have S28: "\<cmnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S27 S28 have S29: "\<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_mpbi)
   from S29 have S30: "\<not> ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> \<in> \<real> ) )" by (rule MMI_intnan)
   from S30 have S31: "\<not> ( ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cmnf> ) )" by (rule MMI_intnanr)
   have S32: "\<cpnf> \<noteq> \<cmnf>" by (rule MMI_pnfnemnf)
   have S33: "\<cpnf> \<noteq> \<cmnf> \<longleftrightarrow> \<cmnf> \<noteq> \<cpnf>" by (rule MMI_necom)
   from S32 S33 have S34: "\<cmnf> \<noteq> \<cpnf>" by (rule MMI_mpbi)
   have S35: "\<cmnf> \<noteq> \<cpnf> \<longleftrightarrow> \<not> ( \<cmnf> = \<cpnf> )" by (rule MMI_df_ne)
   from S34 S35 have S36: "\<not> ( \<cmnf> = \<cpnf> )" by (rule MMI_mpbi)
   from S36 have S37: "\<not> ( ( \<cmnf> = \<cmnf> \<and> \<cmnf> = \<cpnf> ) )" by (rule MMI_intnan)
   from S31 S37 have S38: "\<not> ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cmnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) )" by (rule MMI_pm3_2ni)
   from S29 have S39: "\<not> ( \<cmnf> \<in> \<real> )" .
   from S39 have S40: "\<not> ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> = \<cpnf> ) )" by (rule MMI_intnanr)
   from S29 have S41: "\<not> ( \<cmnf> \<in> \<real> )" .
   from S41 have S42: "\<not> ( ( \<cmnf> = \<cmnf> \<and> \<cmnf> \<in> \<real> ) )" by (rule MMI_intnan)
   from S40 S42 have S43: "\<not> ( ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) )" by (rule MMI_pm3_2ni)
   from S38 S43 have S44: "\<not> ( ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cmnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) ) )" by (rule MMI_pm3_2ni)
   have S45: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S46: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S47: "( \<cmnf> \<in> \<real>\<^sup>* \<and> \<cmnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cmnf> \<ls> \<cmnf> \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cmnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S45 S46 S47 have S48: "\<cmnf> \<ls> \<cmnf> \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cmnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) )" by (rule MMI_mp2an)
   from S44 S48 have S49: "\<not> ( \<cmnf> \<ls> \<cmnf> )" by (rule MMI_mtbir)
   have S50: "( A = \<cmnf> \<and> A = \<cmnf> ) \<longrightarrow> ( A \<ls> A \<longleftrightarrow> \<cmnf> \<ls> \<cmnf> )" by (rule MMI_breq12)
   from S50 have S51: "A = \<cmnf> \<longrightarrow> ( A \<ls> A \<longleftrightarrow> \<cmnf> \<ls> \<cmnf> )" by (rule MMI_anidms)
   from S49 S51 have S52: "A = \<cmnf> \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_mtbiri)
   from S2 S26 S52 have S53: "( A \<in> \<real> \<or> A =   
 \<cpnf> \<or> A = \<cmnf> ) \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_3jaoi)
   from S1 S53 show "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_sylbi)
qed

lemma (in MMIsar0) MMI_ltpnft: 
   shows "A \<in> \<real> \<longrightarrow> A \<ls> \<cpnf>"
proof -
   have S1: "\<cpnf> = \<cpnf>" by (rule MMI_eqid)
   from S1 have S2: "A \<in> \<real> \<longrightarrow> ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> )" by (rule MMI_jctr)
   have S3: "( A \<in> \<real> \<and> \<cpnf> =   
 \<cpnf> ) \<longrightarrow>   
 ( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) )" by (rule MMI_orc)
   have S4: "( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) \<longrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> A \<lsr> \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) )" by (rule MMI_olc)
   from S2 S3 S4 have S5: "A \<in> \<real> \<longrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> A \<lsr> \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) )" by (rule MMI_3syl)
   have S6: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S7: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S8: "( A \<in> \<real>\<^sup>* \<and> \<cpnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> A \<lsr> \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S7 S8 have S9: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( A \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> A \<lsr> \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) ) )" by (rule MMI_mpan2)
   from S6 S9 have S10: "A \<in> \<real> \<longrightarrow>   
 ( A \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> A \<lsr> \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) ) )" by (rule MMI_syl)
   from S5 S10 show "A \<in> \<real> \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_mpbird)
qed

lemma (in MMIsar0) MMI_mnfltt: 
   shows "A \<in> \<real> \<longrightarrow> \<cmnf> \<ls> A"
proof -
   have S1: "\<cmnf> = \<cmnf>" by (rule MMI_eqid)
   from S1 have S2: "A \<in> \<real> \<longrightarrow> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> )" by (rule MMI_jctl)
   have S3: "( \<cmnf> =   
 \<cmnf> \<and> A \<in> \<real> ) \<longrightarrow>   
 ( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) )" by (rule MMI_olc)
   have S4: "( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) ) \<longrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cmnf> \<lsr> A ) \<or> ( \<cmnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) ) )" by (rule MMI_olc)
   from S2 S3 S4 have S5: "A \<in> \<real> \<longrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cmnf> \<lsr> A ) \<or> ( \<cmnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) ) )" by (rule MMI_3syl)
   have S6: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S7: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S8: "( \<cmnf> \<in> \<real>\<^sup>* \<and> A \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cmnf> \<ls> A \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cmnf> \<lsr> A ) \<or> ( \<cmnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S7 S8 have S9: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( \<cmnf> \<ls> A \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cmnf> \<lsr> A ) \<or> ( \<cmnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) ) ) )" by (rule MMI_mpan)
   from S6 S9 have S10: "A \<in> \<real> \<longrightarrow>   
 ( \<cmnf> \<ls> A \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cmnf> \<lsr> A ) \<or> ( \<cmnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> A \<in> \<real> ) ) ) )" by (rule MMI_syl)
   from S5 S10 show "A \<in> \<real> \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_mpbird)
qed

lemma (in MMIsar0) MMI_mnfltpnf: 
   shows "\<cmnf> \<ls> \<cpnf>"
proof -
   have S1: "\<cmnf> = \<cmnf>" by (rule MMI_eqid)
   have S2: "\<cpnf> = \<cpnf>" by (rule MMI_eqid)
   have S3: "( \<cmnf> =   
 \<cmnf> \<and> \<cpnf> =   
 \<cpnf> ) \<longrightarrow>   
 ( ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) )" by (rule MMI_olc)
   from S1 S2 S3 have S4: "( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> =   
 \<cmnf> \<and> \<cpnf> = \<cpnf> )" by (rule MMI_mp2an)
   have S5: "( ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<longrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) )" by (rule MMI_orc)
   from S4 S5 have S6: "( ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) )" by (rule MMI_ax_mp)
   have S7: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S8: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S9: "( \<cmnf> \<in> \<real>\<^sup>* \<and> \<cpnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cmnf> \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S7 S8 S9 have S10: "\<cmnf> \<ls> \<cpnf> \<longleftrightarrow>   
 ( ( ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> \<in> \<real> ) \<and> \<cmnf> \<lsr> \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> = \<cpnf> ) ) \<or> ( ( \<cmnf> \<in> \<real> \<and> \<cpnf> = \<cpnf> ) \<or> ( \<cmnf> = \<cmnf> \<and> \<cpnf> \<in> \<real> ) ) )" by (rule MMI_mp2an)
   from S6 S10 show "\<cmnf> \<ls> \<cpnf>" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_mnfltxrt: 
   shows "( A \<in> \<real> \<or> A = \<cpnf> ) \<longrightarrow> \<cmnf> \<ls> A"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_mnfltt)
   have S2: "\<cmnf> \<ls> \<cpnf>" by (rule MMI_mnfltpnf)
   have S3: "A = \<cpnf> \<longrightarrow> ( \<cmnf> \<ls> A \<longleftrightarrow> \<cmnf> \<ls> \<cpnf> )" by (rule MMI_breq2)
   from S2 S3 have S4: "A = \<cpnf> \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_mpbiri)
   from S1 S4 show "( A \<in> \<real> \<or> A = \<cpnf> ) \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_jaoi)
qed

lemma (in MMIsar0) MMI_pnfnltt: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> A )"
proof -
   have S1: "\<cpnf> \<notin> \<real>" by (rule MMI_pnfnre)
   have S2: "\<cpnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S1 S2 have S3: "\<not> ( \<cpnf> \<in> \<real> )" by (rule MMI_mpbi)
   from S3 have S4: "\<not> ( ( \<cpnf> \<in> \<real> \<and> A \<in> \<real> ) )" by (rule MMI_intnanr)
   from S4 have S5: "\<not> ( ( ( \<cpnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cpnf> \<lsr> A ) )" by (rule MMI_intnanr)
   have S6: "\<cpnf> \<noteq> \<cmnf>" by (rule MMI_pnfnemnf)
   have S7: "\<cpnf> \<noteq> \<cmnf> \<longleftrightarrow> \<not> ( \<cpnf> = \<cmnf> )" by (rule MMI_df_ne)
   from S6 S7 have S8: "\<not> ( \<cpnf> = \<cmnf> )" by (rule MMI_mpbi)
   from S8 have S9: "\<not> ( ( \<cpnf> = \<cmnf> \<and> A = \<cpnf> ) )" by (rule MMI_intnanr)
   from S5 S9 have S10: "\<not> ( ( ( ( \<cpnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cpnf> \<lsr> A ) \<or> ( \<cpnf> = \<cmnf> \<and> A = \<cpnf> ) ) )" by (rule MMI_pm3_2ni)
   from S3 have S11: "\<not> ( \<cpnf> \<in> \<real> )" .
   from S11 have S12: "\<not> ( ( \<cpnf> \<in> \<real> \<and> A = \<cpnf> ) )" by (rule MMI_intnanr)
   from S8 have S13: "\<not> ( \<cpnf> = \<cmnf> )" .
   from S13 have S14: "\<not> ( ( \<cpnf> = \<cmnf> \<and> A \<in> \<real> ) )" by (rule MMI_intnanr)
   from S12 S14 have S15: "\<not> ( ( ( \<cpnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> A \<in> \<real> ) ) )" by (rule MMI_pm3_2ni)
   from S10 S15 have S16: "\<not> ( ( ( ( ( \<cpnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cpnf> \<lsr> A ) \<or> ( \<cpnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cpnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> A \<in> \<real> ) ) ) )" by (rule MMI_pm3_2ni)
   have S17: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S18: "( \<cpnf> \<in> \<real>\<^sup>* \<and> A \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cpnf> \<ls> A \<longleftrightarrow>   
 ( ( ( ( \<cpnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cpnf> \<lsr> A ) \<or> ( \<cpnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cpnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> A \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S17 S18 have S19: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( \<cpnf> \<ls> A \<longleftrightarrow>   
 ( ( ( ( \<cpnf> \<in> \<real> \<and> A \<in> \<real> ) \<and> \<cpnf> \<lsr> A ) \<or> ( \<cpnf> = \<cmnf> \<and> A = \<cpnf> ) ) \<or> ( ( \<cpnf> \<in> \<real> \<and> A = \<cpnf> ) \<or> ( \<cpnf> = \<cmnf> \<and> A \<in> \<real> ) ) ) )" by (rule MMI_mpan)
   from S16 S19 show "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> A )" by (rule MMI_mtbiri)
qed

lemma (in MMIsar0) MMI_nltmnft: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> \<cmnf> )"
proof -
   have S1: "\<cmnf> \<notin> \<real>" by (rule MMI_minfnre)
   have S2: "\<cmnf> \<notin> \<real> \<longleftrightarrow> \<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_df_nel)
   from S1 S2 have S3: "\<not> ( \<cmnf> \<in> \<real> )" by (rule MMI_mpbi)
   from S3 have S4: "\<not> ( ( A \<in> \<real> \<and> \<cmnf> \<in> \<real> ) )" by (rule MMI_intnan)
   from S4 have S5: "\<not> ( ( ( A \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> A \<lsr> \<cmnf> ) )" by (rule MMI_intnanr)
   have S6: "\<cpnf> \<noteq> \<cmnf>" by (rule MMI_pnfnemnf)
   have S7: "\<cpnf> \<noteq> \<cmnf> \<longleftrightarrow> \<cmnf> \<noteq> \<cpnf>" by (rule MMI_necom)
   from S6 S7 have S8: "\<cmnf> \<noteq> \<cpnf>" by (rule MMI_mpbi)
   have S9: "\<cmnf> \<noteq> \<cpnf> \<longleftrightarrow> \<not> ( \<cmnf> = \<cpnf> )" by (rule MMI_df_ne)
   from S8 S9 have S10: "\<not> ( \<cmnf> = \<cpnf> )" by (rule MMI_mpbi)
   from S10 have S11: "\<not> ( ( A = \<cmnf> \<and> \<cmnf> = \<cpnf> ) )" by (rule MMI_intnan)
   from S5 S11 have S12: "\<not> ( ( ( ( A \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> A \<lsr> \<cmnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) )" by (rule MMI_pm3_2ni)
   from S10 have S13: "\<not> ( \<cmnf> = \<cpnf> )" .
   from S13 have S14: "\<not> ( ( A \<in> \<real> \<and> \<cmnf> = \<cpnf> ) )" by (rule MMI_intnan)
   from S3 have S15: "\<not> ( \<cmnf> \<in> \<real> )" .
   from S15 have S16: "\<not> ( ( A = \<cmnf> \<and> \<cmnf> \<in> \<real> ) )" by (rule MMI_intnan)
   from S14 S16 have S17: "\<not> ( ( ( A \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) )" by (rule MMI_pm3_2ni)
   from S12 S17 have S18: "\<not> ( ( ( ( ( A \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> A \<lsr> \<cmnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) ) )" by (rule MMI_pm3_2ni)
   have S19: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S20: "( A \<in> \<real>\<^sup>* \<and> \<cmnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> \<cmnf> \<longleftrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> A \<lsr> \<cmnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) ) )" by (rule MMI_ltxrt)
   from S19 S20 have S21: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( A \<ls> \<cmnf> \<longleftrightarrow>   
 ( ( ( ( A \<in> \<real> \<and> \<cmnf> \<in> \<real> ) \<and> A \<lsr> \<cmnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> = \<cpnf> ) ) \<or> ( ( A \<in> \<real> \<and> \<cmnf> = \<cpnf> ) \<or> ( A = \<cmnf> \<and> \<cmnf> \<in> \<real> ) ) ) )" by (rule MMI_mpan2)
   from S18 S21 show "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_mtbiri)
qed

lemma (in MMIsar0) MMI_pnfget: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> A \<lsq> \<cpnf>"
proof -
   have S1: "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> A )" by (rule MMI_pnfnltt)
   have S2: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S3: "( A \<in> \<real>\<^sup>* \<and> \<cpnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> \<cpnf> \<longleftrightarrow> \<not> ( \<cpnf> \<ls> A ) )" by (rule MMI_xrlenltt)
   from S2 S3 have S4: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<lsq> \<cpnf> \<longleftrightarrow> \<not> ( \<cpnf> \<ls> A ) )" by (rule MMI_mpan2)
   from S1 S4 show "A \<in> \<real>\<^sup>* \<longrightarrow> A \<lsq> \<cpnf>" by (rule MMI_mpbird)
qed

(***********271-280*********************************)

lemma (in MMIsar0) MMI_mnflet: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> \<cmnf> \<lsq> A"
proof -
   have S1: "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_nltmnft)
   have S2: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S3: "( \<cmnf> \<in> \<real>\<^sup>* \<and> A \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cmnf> \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> \<cmnf> ) )" by (rule MMI_xrlenltt)
   from S2 S3 have S4: "A \<in> \<real>\<^sup>* \<longrightarrow> ( \<cmnf> \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> \<cmnf> ) )" by (rule MMI_mpan)
   from S1 S4 show "A \<in> \<real>\<^sup>* \<longrightarrow> \<cmnf> \<lsq> A" by (rule MMI_mpbird)
qed

lemma (in MMIsar0) MMI_xrltnsymt: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_ltnsymt)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S3: "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> A )" by (rule MMI_pnfnltt)
   from S2 S3 have S4: "A \<in> \<real> \<longrightarrow> \<not> ( \<cpnf> \<ls> A )" by (rule MMI_syl)
   from S4 have S5: "( A \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> \<not> ( \<cpnf> \<ls> A )" by (rule MMI_adantr)
   have S6: "B = \<cpnf> \<longrightarrow> ( B \<ls> A \<longleftrightarrow> \<cpnf> \<ls> A )" by (rule MMI_breq1)
   from S6 have S7: "( A \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> \<cpnf> \<ls> A )" by (rule MMI_adantl)
   from S5 S7 have S8: "( A \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> \<not> ( B \<ls> A )" by (rule MMI_mtbird)
   from S8 have S9: "( A \<in> \<real> \<and> B =   
 \<cpnf> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_a1d)
   from S2 have S10: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" .
   have S11: "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_nltmnft)
   from S10 S11 have S12: "A \<in> \<real> \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_syl)
   from S12 have S13: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_adantr)
   have S14: "B = \<cmnf> \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> \<cmnf> )" by (rule MMI_breq2)
   from S14 have S15: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> \<cmnf> )" by (rule MMI_adantl)
   from S13 S15 have S16: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> \<not> ( A \<ls> B )" by (rule MMI_mtbird)
   from S16 have S17: "( A \<in> \<real> \<and> B =   
 \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_pm2_21d)
   from S1 S9 S17 have S18: "( A \<in> \<real> \<and> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> ) ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_3jaodan)
   have S19: "B \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> B )" by (rule MMI_pnfnltt)
   from S19 have S20: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> \<not> ( \<cpnf> \<ls> B )" by (rule MMI_adantl)
   have S21: "A = \<cpnf> \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cpnf> \<ls> B )" by (rule MMI_breq1)
   from S21 have S22: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cpnf> \<ls> B )" by (rule MMI_adantr)
   from S20 S22 have S23: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> \<not> ( A \<ls> B )" by (rule MMI_mtbird)
   from S23 have S24: "( A =   
 \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_pm2_21d)
   have S25: "B \<in> \<real>\<^sup>* \<longleftrightarrow> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> )" by (rule MMI_elxr)
   from S24 S25 have S26: "( A =   
 \<cpnf> \<and> ( B \<in> \<real> \<or> B =   
 \<cpnf> \<or> B =   
 \<cmnf> ) ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_sylan2br)
   have S27: "B \<in> \<real> \<longrightarrow> B \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S28: "B \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( B \<ls> \<cmnf> )" by (rule MMI_nltmnft)
   from S27 S28 have S29: "B \<in> \<real> \<longrightarrow> \<not> ( B \<ls> \<cmnf> )" by (rule MMI_syl)
   from S29 have S30: "( A = \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> \<not> ( B \<ls> \<cmnf> )" by (rule MMI_adantl)
   have S31: "A = \<cmnf> \<longrightarrow> ( B \<ls> A \<longleftrightarrow> B \<ls> \<cmnf> )" by (rule MMI_breq2)
   from S31 have S32: "( A = \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> B \<ls> \<cmnf> )" by (rule MMI_adantr)
   from S30 S32 have S33: "( A = \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> \<not> ( B \<ls> A )" by (rule MMI_mtbird)
   from S33 have S34: "( A =   
 \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_a1d)
   have S35: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S36: "\<cmnf> \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> \<cmnf> )" by (rule MMI_pnfnltt)
   from S35 S36 have S37: "\<not> ( \<cpnf> \<ls> \<cmnf> )" by (rule MMI_ax_mp)
   have S38: "( B = \<cpnf> \<and> A = \<cmnf> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> \<cpnf> \<ls> \<cmnf> )" by (rule MMI_breq12)
   from S37 S38 have S39: "( B = \<cpnf> \<and> A = \<cmnf> ) \<longrightarrow> \<not> ( B \<ls> A )" by (rule MMI_mtbiri)
   from S39 have S40: "( A = \<cmnf> \<and> B = \<cpnf> ) \<longrightarrow> \<not> ( B \<ls> A )" by (rule MMI_ancoms)
   from S40 have S41: "( A =   
 \<cmnf> \<and> B = \<cpnf> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_a1d)
   have S42: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S43: "\<cmnf> \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cmnf> \<ls> \<cmnf> )" by (rule MMI_xrltnrt)
   from S42 S43 have S44: "\<not> ( \<cmnf> \<ls> \<cmnf> )" by (rule MMI_ax_mp)
   have S45: "( A = \<cmnf> \<and> B = \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cmnf> \<ls> \<cmnf> )" by (rule MMI_breq12)
   from S44 S45 have S46: "( A = \<cmnf> \<and> B = \<cmnf> ) \<longrightarrow> \<not> ( A \<ls> B )" by (rule MMI_mtbiri)
   from S46 have S47: "( A =   
 \<cmnf> \<and> B = \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_pm2_21d)
   from S34 S41 S47 have S48: "( A =   
 \<cmnf> \<and> ( B \<in> \<real> \<or> B =   
 \<cpnf> \<or> B =   
 \<cmnf> ) ) \<longrightarrow> ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_3jaodan)
   from S18 S26 S48 have S49: "( ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> ) \<and> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> ) ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_3jaoian)
   have S50: "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" by (rule MMI_elxr)
   from S25 have S51: "B \<in> \<real>\<^sup>* \<longleftrightarrow> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> )" .
   from S49 S50 S51 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_syl2anb)
qed

lemma (in MMIsar0) MMI_xrlttrit: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<ls> A ) ) )"
proof -
   have S1: "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_xrltnrt)
   from S1 have S2: "( A \<in> \<real>\<^sup>* \<and> A = B ) \<longrightarrow> \<not> ( A \<ls> A )" by (rule MMI_adantr)
   have S3: "A = B \<longrightarrow> ( A \<ls> A \<longleftrightarrow> A \<ls> B )" by (rule MMI_breq2)
   from S3 have S4: "( A \<in> \<real>\<^sup>* \<and> A = B ) \<longrightarrow> ( A \<ls> A \<longleftrightarrow> A \<ls> B )" by (rule MMI_adantl)
   from S2 S4 have S5: "( A \<in> \<real>\<^sup>* \<and> A = B ) \<longrightarrow> \<not> ( A \<ls> B )" by (rule MMI_mtbid)
   from S5 have S6: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = B \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_ex)
   from S6 have S7: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A = B \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_adantr)
   have S8: "( B \<in> \<real>\<^sup>* \<and> A \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<ls> A \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_xrltnsymt)
   from S8 have S9: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<ls> A \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_ancoms)
   from S7 S9 have S10: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A = B \<or> B \<ls> A ) \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_jaod)
   have S11: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<ls> A ) ) )" by (rule MMI_axlttri)
   from S11 have S12: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( ( A = B \<or> B \<ls> A ) ) \<longrightarrow> A \<ls> B )" by (rule MMI_biimprd)
   from S12 have S13: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_con1d)
   have S14: "A \<in> \<real> \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_ltpnft)
   from S14 have S15: "( A \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_adantr)
   have S16: "B = \<cpnf> \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> \<cpnf> )" by (rule MMI_breq2)
   from S16 have S17: "( A \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> \<cpnf> )" by (rule MMI_adantl)
   from S15 S17 have S18: "( A \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> A \<ls> B" by (rule MMI_mpbird)
   from S18 have S19: "( A \<in> \<real> \<and> B =   
 \<cpnf> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_pm2_21nd)
   have S20: "A \<in> \<real> \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_mnfltt)
   from S20 have S21: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_adantr)
   have S22: "B = \<cmnf> \<longrightarrow> ( B \<ls> A \<longleftrightarrow> \<cmnf> \<ls> A )" by (rule MMI_breq1)
   from S22 have S23: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> \<cmnf> \<ls> A )" by (rule MMI_adantl)
   from S21 S23 have S24: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> B \<ls> A" by (rule MMI_mpbird)
   have S25: "B \<ls> A \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_olc)
   from S24 S25 have S26: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_syl)
   from S26 have S27: "( A \<in> \<real> \<and> B =   
 \<cmnf> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_a1d)
   from S13 S19 S27 have S28: "( A \<in> \<real> \<and> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> ) ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_3jaodan)
   have S29: "B \<in> \<real> \<longrightarrow> B \<ls> \<cpnf>" by (rule MMI_ltpnft)
   from S29 have S30: "( A = \<cpnf> \<and> B \<in> \<real> ) \<longrightarrow> B \<ls> \<cpnf>" by (rule MMI_adantl)
   have S31: "A = \<cpnf> \<longrightarrow> ( B \<ls> A \<longleftrightarrow> B \<ls> \<cpnf> )" by (rule MMI_breq2)
   from S31 have S32: "( A = \<cpnf> \<and> B \<in> \<real> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> B \<ls> \<cpnf> )" by (rule MMI_adantr)
   from S30 S32 have S33: "( A = \<cpnf> \<and> B \<in> \<real> ) \<longrightarrow> B \<ls> A" by (rule MMI_mpbird)
   from S25 have S34: "B \<ls> A \<longrightarrow> ( A = B \<or> B \<ls> A )" .
   from S33 S34 have S35: "( A = \<cpnf> \<and> B \<in> \<real> ) \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_syl)
   from S35 have S36: "( A =   
 \<cpnf> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_a1d)
   have S37: "( A = \<cpnf> \<and> B = \<cpnf> ) \<longrightarrow> A = B" by (rule MMI_eqtr3t)
   have S38: "A = B \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_orc)
   from S37 S38 have S39: "( A = \<cpnf> \<and> B = \<cpnf> ) \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_syl)
   from S39 have S40: "( A =   
 \<cpnf> \<and> B =   
 \<cpnf> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_a1d)
   have S41: "\<cmnf> \<ls> \<cpnf>" by (rule MMI_mnfltpnf)
   have S42: "( B = \<cmnf> \<and> A = \<cpnf> ) \<longrightarrow> ( B \<ls> A \<longleftrightarrow> \<cmnf> \<ls> \<cpnf> )" by (rule MMI_breq12)
   from S41 S42 have S43: "( B = \<cmnf> \<and> A = \<cpnf> ) \<longrightarrow> B \<ls> A" by (rule MMI_mpbiri)
   from S43 have S44: "( A = \<cpnf> \<and> B = \<cmnf> ) \<longrightarrow> B \<ls> A" by (rule MMI_ancoms)
   from S25 have S45: "B \<ls> A \<longrightarrow> ( A = B \<or> B \<ls> A )" .
   from S44 S45 have S46: "( A = \<cpnf> \<and> B = \<cmnf> ) \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_syl)
   from S46 have S47: "( A =   
 \<cpnf> \<and> B =   
 \<cmnf> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_a1d)
   from S36 S40 S47 have S48: "( A =   
 \<cpnf> \<and> ( B \<in> \<real> \<or> B =   
 \<cpnf> \<or> B =   
 \<cmnf> ) ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_3jaodan)
   have S49: "B \<in> \<real> \<longrightarrow> \<cmnf> \<ls> B" by (rule MMI_mnfltt)
   from S49 have S50: "( A = \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> \<cmnf> \<ls> B" by (rule MMI_adantl)
   have S51: "A = \<cmnf> \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cmnf> \<ls> B )" by (rule MMI_breq1)
   from S51 have S52: "( A = \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cmnf> \<ls> B )" by (rule MMI_adantr)
   from S50 S52 have S53: "( A = \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow> A \<ls> B" by (rule MMI_mpbird)
   from S53 have S54: "( A =   
 \<cmnf> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_pm2_21nd)
   have S55: "\<cmnf> \<ls> \<cpnf>" by (rule MMI_mnfltpnf)
   have S56: "( A = \<cmnf> \<and> B = \<cpnf> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cmnf> \<ls> \<cpnf> )" by (rule MMI_breq12)
   from S55 S56 have S57: "( A = \<cmnf> \<and> B = \<cpnf> ) \<longrightarrow> A \<ls> B" by (rule MMI_mpbiri)
   from S57 have S58: "( A =   
 \<cmnf> \<and> B =   
 \<cpnf> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_pm2_21nd)
   have S59: "( A = \<cmnf> \<and> B = \<cmnf> ) \<longrightarrow> A = B" by (rule MMI_eqtr3t)
   from S38 have S60: "A = B \<longrightarrow> ( A = B \<or> B \<ls> A )" .
   from S59 S60 have S61: "( A = \<cmnf> \<and> B = \<cmnf> ) \<longrightarrow> ( A = B \<or> B \<ls> A )" by (rule MMI_syl)
   from S61 have S62: "( A =   
 \<cmnf> \<and> B =   
 \<cmnf> ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_a1d)
   from S54 S58 S62 have S63: "( A =   
 \<cmnf> \<and> ( B \<in> \<real> \<or> B =   
 \<cpnf> \<or> B =   
 \<cmnf> ) ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_3jaodan)
   from S28 S48 S63 have S64: "( ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> ) \<and> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> ) ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_3jaoian)
   have S65: "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" by (rule MMI_elxr)
   have S66: "B \<in> \<real>\<^sup>* \<longleftrightarrow> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> )" by (rule MMI_elxr)
   from S64 S65 S66 have S67: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> ( A = B \<or> B \<ls> A ) )" by (rule MMI_syl2anb)
   from S10 S67 have S68: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A = B \<or> B \<ls> A ) \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_impbid)
   from S68 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( ( A = B \<or> B \<ls> A ) ) )" by (rule MMI_con2bid)
qed

lemma (in MMIsar0) MMI_xrlttrt: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )"
proof -
   have S1: "( A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_axlttrn)
   from S1 have S2: "( ( A \<in> \<real> \<and> B \<in> \<real> ) \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3expa)
   from S2 have S3: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_an1rs)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S5: "C \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> C )" by (rule MMI_pnfnltt)
   from S4 S5 have S6: "C \<in> \<real> \<longrightarrow> \<not> ( \<cpnf> \<ls> C )" by (rule MMI_syl)
   from S6 have S7: "( C \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> \<not> ( \<cpnf> \<ls> C )" by (rule MMI_adantr)
   have S8: "B = \<cpnf> \<longrightarrow> ( B \<ls> C \<longleftrightarrow> \<cpnf> \<ls> C )" by (rule MMI_breq1)
   from S8 have S9: "( C \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> ( B \<ls> C \<longleftrightarrow> \<cpnf> \<ls> C )" by (rule MMI_adantl)
   from S7 S9 have S10: "( C \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> \<not> ( B \<ls> C )" by (rule MMI_mtbird)
   from S10 have S11: "( C \<in> \<real> \<and> B = \<cpnf> ) \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C )" by (rule MMI_pm2_21d)
   from S11 have S12: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> B =   
 \<cpnf> ) \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C )" by (rule MMI_adantll)
   from S12 have S13: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> B =   
 \<cpnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantld)
   have S14: "A \<in> \<real> \<longrightarrow> A \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   have S15: "A \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_nltmnft)
   from S14 S15 have S16: "A \<in> \<real> \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_syl)
   from S16 have S17: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> \<not> ( A \<ls> \<cmnf> )" by (rule MMI_adantr)
   have S18: "B = \<cmnf> \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> \<cmnf> )" by (rule MMI_breq2)
   from S18 have S19: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> \<cmnf> )" by (rule MMI_adantl)
   from S17 S19 have S20: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> \<not> ( A \<ls> B )" by (rule MMI_mtbird)
   from S20 have S21: "( A \<in> \<real> \<and> B = \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C )" by (rule MMI_pm2_21d)
   from S21 have S22: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> B =   
 \<cmnf> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C )" by (rule MMI_adantlr)
   from S22 have S23: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> B =   
 \<cmnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantrd)
   from S3 S13 S23 have S24: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3jaodan)
   have S25: "B \<in> \<real>\<^sup>* \<longleftrightarrow> ( B \<in> \<real> \<or> B = \<cpnf> \<or> B = \<cmnf> )" by (rule MMI_elxr)
   from S24 S25 have S26: "( ( A \<in> \<real> \<and> C \<in> \<real> ) \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_sylan2b)
   from S26 have S27: "( ( A \<in> \<real> \<and> B \<in> \<real>\<^sup>* ) \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_an1rs)
   have S28: "A \<in> \<real> \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_ltpnft)
   from S28 have S29: "( A \<in> \<real> \<and> C = \<cpnf> ) \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_adantr)
   have S30: "C = \<cpnf> \<longrightarrow> ( A \<ls> C \<longleftrightarrow> A \<ls> \<cpnf> )" by (rule MMI_breq2)
   from S30 have S31: "( A \<in> \<real> \<and> C = \<cpnf> ) \<longrightarrow> ( A \<ls> C \<longleftrightarrow> A \<ls> \<cpnf> )" by (rule MMI_adantl)
   from S29 S31 have S32: "( A \<in> \<real> \<and> C = \<cpnf> ) \<longrightarrow> A \<ls> C" by (rule MMI_mpbird)
   from S32 have S33: "( ( A \<in> \<real> \<and> B \<in> \<real>\<^sup>* ) \<and> C = \<cpnf> ) \<longrightarrow> A \<ls> C" by (rule MMI_adantlr)
   from S33 have S34: "( ( A \<in> \<real> \<and> B \<in> \<real>\<^sup>* ) \<and> C =   
 \<cpnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_a1d)
   have S35: "B \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( B \<ls> \<cmnf> )" by (rule MMI_nltmnft)
   from S35 have S36: "( B \<in> \<real>\<^sup>* \<and> C = \<cmnf> ) \<longrightarrow> \<not> ( B \<ls> \<cmnf> )" by (rule MMI_adantr)
   have S37: "C = \<cmnf> \<longrightarrow> ( B \<ls> C \<longleftrightarrow> B \<ls> \<cmnf> )" by (rule MMI_breq2)
   from S37 have S38: "( B \<in> \<real>\<^sup>* \<and> C = \<cmnf> ) \<longrightarrow> ( B \<ls> C \<longleftrightarrow> B \<ls> \<cmnf> )" by (rule MMI_adantl)
   from S36 S38 have S39: "( B \<in> \<real>\<^sup>* \<and> C = \<cmnf> ) \<longrightarrow> \<not> ( B \<ls> C )" by (rule MMI_mtbird)
   from S39 have S40: "( B \<in> \<real>\<^sup>* \<and> C = \<cmnf> ) \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C )" by (rule MMI_pm2_21d)
   from S40 have S41: "( B \<in> \<real>\<^sup>* \<and> C =   
 \<cmnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantld)
   from S41 have S42: "( ( A \<in> \<real> \<and> B \<in> \<real>\<^sup>* ) \<and> C =   
 \<cmnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantll)
   from S27 S34 S42 have S43: "( ( A \<in> \<real> \<and> B \<in> \<real>\<^sup>* ) \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3jaodan)
   from S43 have S44: "( A \<in> \<real> \<and> ( B \<in> \<real>\<^sup>* \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_anasss)
   have S45: "B \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> B )" by (rule MMI_pnfnltt)
   from S45 have S46: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> \<not> ( \<cpnf> \<ls> B )" by (rule MMI_adantl)
   have S47: "A = \<cpnf> \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cpnf> \<ls> B )" 
     by (rule MMI_breq1)
   from S47 have S48: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> B \<longleftrightarrow> \<cpnf> \<ls> B )" by (rule MMI_adantr)
   from S46 S48 have S49: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> \<not> ( A \<ls> B )" 
     by (rule MMI_mtbird)
   from S49 have S50: "( A = \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C )" 
     by (rule MMI_pm2_21d)
   from S50 have S51: "( A =   
 \<cpnf> \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantrd)
   from S51 have S52: "( A =   
 \<cpnf> \<and> ( B \<in> \<real>\<^sup>* \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantrr)
   have S53: "C \<in> \<real> \<longrightarrow> \<cmnf> \<ls> C" by (rule MMI_mnfltt)
   from S53 have S54: "( A = \<cmnf> \<and> C \<in> \<real> ) \<longrightarrow> \<cmnf> \<ls> C" 
     by (rule MMI_adantl)
   have S55: "A = \<cmnf> \<longrightarrow> ( A \<ls> C \<longleftrightarrow> \<cmnf> \<ls> C )" 
     by (rule MMI_breq1)
   from S55 have S56: "( A = \<cmnf> \<and> C \<in> \<real> ) \<longrightarrow> ( A \<ls> C \<longleftrightarrow> \<cmnf> \<ls> C )" by (rule MMI_adantr)
   from S54 S56 have S57: "( A = \<cmnf> \<and> C \<in> \<real> ) \<longrightarrow> A \<ls> C" 
     by (rule MMI_mpbird)
   from S57 have S58: "( A =   
 \<cmnf> \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_a1d)
   from S58 have S59: "( ( A = \<cmnf> \<and> B \<in> \<real>\<^sup>* ) \<and> C \<in> \<real> ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantlr)
   have S60: "\<cmnf> \<ls> \<cpnf>" by (rule MMI_mnfltpnf)
   have S61: 
     "( A = \<cmnf> \<and> C = \<cpnf> ) \<longrightarrow> ( A \<ls> C \<longleftrightarrow> \<cmnf> \<ls> \<cpnf> )" 
     by (rule MMI_breq12)
   from S60 S61 have S62: "( A = \<cmnf> \<and> C = \<cpnf> ) \<longrightarrow> A \<ls> C" 
     by (rule MMI_mpbiri)
   from S62 have S63: "( A =   
 \<cmnf> \<and> C =   
 \<cpnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_a1d)
   from S63 have S64: "( ( A = \<cmnf> \<and> B \<in> \<real>\<^sup>* ) \<and> C =   
 \<cpnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantlr)
   from S41 have S65: "( B \<in> \<real>\<^sup>* \<and> C =   
 \<cmnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" .
   from S65 have S66: "( ( A = \<cmnf> \<and> B \<in> \<real>\<^sup>* ) \<and> C =   
 \<cmnf> ) \<longrightarrow> ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_adantll)
   from S59 S64 S66 have S67: 
     "( ( A = \<cmnf> \<and> B \<in> \<real>\<^sup>* ) \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) \<longrightarrow> 
      ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3jaodan)
   from S67 have S68: "( A =   
 \<cmnf> \<and> ( B \<in> \<real>\<^sup>* \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_anasss)
   from S44 S52 S68 have S69: "( ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> ) \<and> ( B \<in> \<real>\<^sup>* \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3jaoian)
   from S69 have S70: "( ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> ) \<and> B \<in> \<real>\<^sup>* \<and> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> ) ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_3impb)
   have S71: "C \<in> \<real>\<^sup>* \<longleftrightarrow> ( C \<in> \<real> \<or> C = \<cpnf> \<or> C = \<cmnf> )" by (rule MMI_elxr)
   from S70 S71 have S72: "( ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> ) \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_syl3an3b)
   have S73: "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" 
     by (rule MMI_elxr)
   from S72 S73 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_syl3an1b)
qed

lemma (in MMIsar0) MMI_xrltso: 
   shows "\<cltrrset> Orders \<real>\<^sup>*"
proof -
  { fix x y z
    have S1: "( x \<in> \<real>\<^sup>* \<and> y \<in> \<real>\<^sup>* ) \<longrightarrow>   
      ( x \<ls> y \<longleftrightarrow> \<not> ( ( x = y \<or> y \<ls> x ) ) )" by (rule MMI_xrlttrit)
    from S1 have S2: "( x \<in> \<real>\<^sup>* \<and> y \<in> \<real>\<^sup>* \<and> z \<in> \<real>\<^sup>* ) \<longrightarrow>   
      ( x \<ls> y \<longleftrightarrow> \<not> ( ( x = y \<or> y \<ls> x ) ) )" by (rule MMI_3adant3)
    have S3: "( x \<in> \<real>\<^sup>* \<and> y \<in> \<real>\<^sup>* \<and> z \<in> \<real>\<^sup>* ) \<longrightarrow>   
      ( ( x \<ls> y \<and> y \<ls> z ) \<longrightarrow> x \<ls> z )" by (rule MMI_xrlttrt)
    from S2 S3 have S4: 
      "( x \<in> \<real>\<^sup>* \<and> y \<in> \<real>\<^sup>* \<and> z \<in> \<real>\<^sup>* ) \<longrightarrow>   ( ( x \<ls> y \<longleftrightarrow> 
      \<not> ( ( x = y \<or> y \<ls> x ) ) ) \<and> ( ( x \<ls> y \<and> y \<ls> z ) \<longrightarrow> 
      x \<ls> z ) )" by (rule MMI_jca)
    then have  "x \<in> \<real>\<^sup>*  \<and> y \<in> \<real>\<^sup>* \<and> z \<in> \<real>\<^sup>*  \<longrightarrow>   
      ( ( \<langle>x,y\<rangle> \<in> \<cltrrset> \<longleftrightarrow> \<not> ( ( x = y \<or> \<langle>y, x\<rangle> \<in> \<cltrrset> ) ) ) \<and> 
      ( ( \<langle>x, y\<rangle> \<in> \<cltrrset>  \<and> \<langle>y, z\<rangle> \<in> \<cltrrset> ) \<longrightarrow> 
      \<langle>x, z\<rangle> \<in> \<cltrrset> ) )"
      using cltrr_def by simp
  } then have "\<forall>x y z. ( x \<in> \<real>\<^sup>*  \<and> y \<in> \<real>\<^sup>* \<and> z \<in> \<real>\<^sup>* ) \<longrightarrow>   
      ( ( \<langle>x,y\<rangle> \<in> \<cltrrset> \<longleftrightarrow> \<not> ( ( x = y \<or> \<langle>y, x\<rangle> \<in> \<cltrrset> ) ) ) \<and> 
      ( ( \<langle>x, y\<rangle> \<in> \<cltrrset>  \<and> \<langle>y, z\<rangle> \<in> \<cltrrset> ) \<longrightarrow> 
      \<langle>x, z\<rangle> \<in> \<cltrrset> ) )" by auto
  thus "\<cltrrset> Orders \<real>\<^sup>*" by (rule MMI_so)
qed

lemma (in MMIsar0) MMI_xrlttri3t: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
  ( A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )"
proof -
   have S1: "\<cltrrset> Orders \<real>\<^sup>*" by (rule MMI_xrltso)
   have "( \<cltrrset> Orders \<real>\<^sup>* \<and> ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> ( \<not> ( \<langle>A,B\<rangle> \<in> \<cltrrset>  ) \<and> \<not> ( \<langle>B, A\<rangle> \<in> \<cltrrset> ) ) )" 
     by (rule MMI_sotrieq2)
   then have S2: "( \<cltrrset> Orders \<real>\<^sup>* \<and> ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" 
     using cltrr_def by simp
   from S1 S2 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
     ( A =   
     B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_xrleloet: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
  ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )"
proof -
   have S1: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_xrlenltt)
   have S2: "( B \<in> \<real>\<^sup>* \<and> A \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<ls> A \<longleftrightarrow> \<not> ( ( B = A \<or> A \<ls> B ) ) )" by (rule MMI_xrlttrit)
   from S2 have S3: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<ls> A \<longleftrightarrow> \<not> ( ( B = A \<or> A \<ls> B ) ) )" by (rule MMI_ancoms)
   from S3 have S4: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( B = A \<or> A \<ls> B ) \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_con2bid)
   have S5: "B = A \<longleftrightarrow> A = B" by (rule MMI_eqcom)
   from S5 have S6: "( B = A \<or> A \<ls> B ) \<longleftrightarrow> ( A = B \<or> A \<ls> B )" by (rule MMI_orbi1i)
   have S7: "( A = B \<or> A \<ls> B ) \<longleftrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_orcom)
   from S6 S7 have S8: "( B = A \<or> A \<ls> B ) \<longleftrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_bitr)
   from S4 S8 have S9: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<not> ( B \<ls> A ) \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_syl5rbbr)
   from S1 S9 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_xrleltnet: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( A = B ) )"
proof -
   have S1: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A =   
 B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" by (rule MMI_xrlttri3t)
   have S2: "( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) \<longrightarrow>   
 \<not> ( A \<ls> B )" by (rule MMI_pm3_26)
   from S1 S2 have S3: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A = B \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_syl6bi)
   from S3 have S4: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A = B \<longrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_adantr)
   have S5: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_xrleloet)
   from S5 have S6: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<or> A = B )" by (rule MMI_biimpa)
   from S6 have S7: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( \<not> ( A \<ls> B ) \<longrightarrow> A = B )" by (rule MMI_ord)
   from S4 S7 have S8: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> \<not> ( A \<ls> B ) )" by (rule MMI_impbid)
   from S8 have S9: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( A = B ) )" by (rule MMI_con2bid)
   from S9 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> A \<lsq> B ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> \<not> ( A = B ) )" by (rule MMI_3impa)
qed

lemma (in MMIsar0) MMI_xrltlet: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<lsq> B )"
proof -
   have S1: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_xrleloet)
   have S2: "A \<ls> B \<longrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_orc)
   from S1 S2 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<lsq> B )" by (rule MMI_syl5bir)
qed

lemma (in MMIsar0) MMI_xrlelttrt: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )"
proof -
   have S1: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_xrleloet)
   from S1 have S2: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_3adant3)
   have S3: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_xrlttrt)
   from S3 have S4: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_exp3a)
   have S5: "A = B \<longrightarrow> ( A \<ls> C \<longleftrightarrow> B \<ls> C )" by (rule MMI_breq1)
   from S5 have S6: "A = B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C )" by (rule MMI_biimprd)
   from S6 have S7: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A = B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_a1i)
   from S4 S7 have S8: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<or> A = B ) \<longrightarrow>   
 ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_jaod)
   from S2 S8 have S9: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_sylbid)
   from S9 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_imp3a)
qed

(**************** 281-290 ***********************)

lemma (in MMIsar0) MMI_xrltletrt: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<lsq> C ) \<longrightarrow> A \<ls> C )"
proof -
   have S1: "( B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_xrleloet)
   from S1 have S2: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_3adant1)
   have S3: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_xrlttrt)
   from S3 have S4: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_exp3a)
   from S4 have S5: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<ls> C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_com23)
   have S6: "B = C \<longrightarrow> ( A \<ls> B \<longleftrightarrow> A \<ls> C )" by (rule MMI_breq2)
   from S6 have S7: "B = C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C )" by (rule MMI_biimpd)
   from S7 have S8: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B = C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_a1i)
   from S5 S8 have S9: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( B \<ls> C \<or> B = C ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_jaod)
   from S2 S9 have S10: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<lsq> C \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<ls> C ) )" by (rule MMI_sylbid)
   from S10 have S11: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> ( B \<lsq> C \<longrightarrow> A \<ls> C ) )" by (rule MMI_com23)
   from S11 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<and> B \<lsq> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_imp3a)
qed

lemma (in MMIsar0) MMI_xrletrt: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> C ) \<longrightarrow> A \<lsq> C )"
proof -
   have S1: "( B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_xrleloet)
   from S1 have S2: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_3adant1)
   from S2 have S3: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B \<lsq> C \<longleftrightarrow> ( B \<ls> C \<or> B = C ) )" by (rule MMI_adantr)
   have S4: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<ls> C )" by (rule MMI_xrlelttrt)
   have S5: "( A \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow> ( A \<ls> C \<longrightarrow> A \<lsq> C )" 
     by (rule MMI_xrltlet)
   from S5 have S6: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> C \<longrightarrow> A \<lsq> C )" by (rule MMI_3adant2)
   from S4 S6 have S7: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_syld)
   from S7 have S8: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( B \<ls> C \<longrightarrow> A \<lsq> C ) )" by (rule MMI_exp3a)
   from S8 have S9: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B \<ls> C \<longrightarrow> A \<lsq> C )" by (rule MMI_imp)
   have S10: "B = C \<longrightarrow> ( A \<lsq> B \<longleftrightarrow> A \<lsq> C )" by (rule MMI_breq2)
   from S10 have S11: "A \<lsq> B \<longrightarrow> ( B = C \<longrightarrow> A \<lsq> C )" 
     by (rule MMI_biimpcd)
   from S11 have S12: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B = C \<longrightarrow> A \<lsq> C )" by (rule MMI_adantl)
   from S9 S12 have S13: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( ( B \<ls> C \<or> B = C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_jaod)
   from S3 S13 have S14: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<and> A \<lsq> B ) \<longrightarrow>   
 ( B \<lsq> C \<longrightarrow> A \<lsq> C )" by (rule MMI_sylbid)
   from S14 have S15: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> B \<longrightarrow> ( B \<lsq> C \<longrightarrow> A \<lsq> C ) )" by (rule MMI_ex)
   from S15 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> C \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<lsq> C ) \<longrightarrow> A \<lsq> C )" by (rule MMI_imp3a)
qed

lemma (in MMIsar0) MMI_xrltnet: 
   shows "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( A = B ) )"
proof -
   have S1: "\<cltrrset> Orders \<real>\<^sup>*" by (rule MMI_xrltso)
   have  "( \<cltrrset> Orders \<real>\<^sup>* \<and> ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> \<not> ( ( \<langle>A, B\<rangle> \<in> \<cltrrset> \<or> \<langle>B,A\<rangle> \<in> \<cltrrset> ) ) )" 
     by (rule MMI_sotrieq)
   then have S2: "( \<cltrrset> Orders \<real>\<^sup>* \<and> ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> \<not> ( ( A \<ls> B \<or> B \<ls> A ) ) )" 
     using cltrr_def by simp
   from S1 S2 have S3: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
     ( A = B \<longleftrightarrow> \<not> ( ( A \<ls> B \<or> B \<ls> A ) ) )" by (rule MMI_mpan)
   from S3 have S4: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<ls> B \<or> B \<ls> A ) \<longleftrightarrow> \<not> ( A = B ) )" by (rule MMI_con2bid)
   have S5: "A \<ls> B \<longrightarrow> ( A \<ls> B \<or> B \<ls> A )" by (rule MMI_orc)
   from S4 S5 show "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( A = B ) )" by (rule MMI_syl5bi)
qed

lemma (in MMIsar0) MMI_nltpnftt: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cpnf> \<longleftrightarrow> \<not> ( A \<ls> \<cpnf> ) )"
proof -
   have S1: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S2: "\<cpnf> \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cpnf> \<ls> \<cpnf> )" by (rule MMI_xrltnrt)
   from S1 S2 have S3: "\<not> ( \<cpnf> \<ls> \<cpnf> )" by (rule MMI_ax_mp)
   have S4: "A = \<cpnf> \<longrightarrow> ( A \<ls> \<cpnf> \<longleftrightarrow> \<cpnf> \<ls> \<cpnf> )" by (rule MMI_breq1)
   from S3 S4 have S5: "A = \<cpnf> \<longrightarrow> \<not> ( A \<ls> \<cpnf> )" by (rule MMI_mtbiri)
   from S5 have S6: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cpnf> \<longrightarrow> \<not> ( A \<ls> \<cpnf> ) )" by (rule MMI_a1i)
   have S7: "A \<in> \<real>\<^sup>* \<longrightarrow> A \<lsq> \<cpnf>" by (rule MMI_pnfget)
   have S8: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S9: "( A \<in> \<real>\<^sup>* \<and> \<cpnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( A \<lsq> \<cpnf> \<longleftrightarrow> ( A \<ls> \<cpnf> \<or> A = \<cpnf> ) )" by (rule MMI_xrleloet)
   from S8 S9 have S10: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<lsq> \<cpnf> \<longleftrightarrow> ( A \<ls> \<cpnf> \<or> A = \<cpnf> ) )" by (rule MMI_mpan2)
   from S7 S10 have S11: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<ls> \<cpnf> \<or> A = \<cpnf> )" by (rule MMI_mpbid)
   from S11 have S12: "A \<in> \<real>\<^sup>* \<longrightarrow> ( \<not> ( A \<ls> \<cpnf> ) \<longrightarrow> A = \<cpnf> )" by (rule MMI_ord)
   from S6 S12 show "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cpnf> \<longleftrightarrow> \<not> ( A \<ls> \<cpnf> ) )" by (rule MMI_impbid)
qed

lemma (in MMIsar0) MMI_ngtmnftt: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cmnf> \<longleftrightarrow> \<not> ( \<cmnf> \<ls> A ) )"
proof -
   have S1: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S2: "\<cmnf> \<in> \<real>\<^sup>* \<longrightarrow> \<not> ( \<cmnf> \<ls> \<cmnf> )" by (rule MMI_xrltnrt)
   from S1 S2 have S3: "\<not> ( \<cmnf> \<ls> \<cmnf> )" by (rule MMI_ax_mp)
   have S4: "A = \<cmnf> \<longrightarrow> ( \<cmnf> \<ls> A \<longleftrightarrow> \<cmnf> \<ls> \<cmnf> )" by (rule MMI_breq2)
   from S3 S4 have S5: "A = \<cmnf> \<longrightarrow> \<not> ( \<cmnf> \<ls> A )" by (rule MMI_mtbiri)
   from S5 have S6: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cmnf> \<longrightarrow> \<not> ( \<cmnf> \<ls> A ) )" by (rule MMI_a1i)
   have S7: "A \<in> \<real>\<^sup>* \<longrightarrow> \<cmnf> \<lsq> A" by (rule MMI_mnflet)
   have S8: "\<cmnf> \<in> \<real>\<^sup>*" by (rule MMI_mnfxr)
   have S9: "( \<cmnf> \<in> \<real>\<^sup>* \<and> A \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( \<cmnf> \<lsq> A \<longleftrightarrow> ( \<cmnf> \<ls> A \<or> \<cmnf> = A ) )" by (rule MMI_xrleloet)
   from S8 S9 have S10: "A \<in> \<real>\<^sup>* \<longrightarrow> ( \<cmnf> \<lsq> A \<longleftrightarrow> ( \<cmnf> \<ls> A \<or> \<cmnf> = A ) )" by (rule MMI_mpan)
   from S7 S10 have S11: "A \<in> \<real>\<^sup>* \<longrightarrow> ( \<cmnf> \<ls> A \<or> \<cmnf> = A )" by (rule MMI_mpbid)
   from S11 have S12: "A \<in> \<real>\<^sup>* \<longrightarrow> ( \<not> ( \<cmnf> \<ls> A ) \<longrightarrow> \<cmnf> = A )" by (rule MMI_ord)
   have S13: "\<cmnf> = A \<longleftrightarrow> A = \<cmnf>" by (rule MMI_eqcom)
   from S12 S13 have S14: "A \<in> \<real>\<^sup>* \<longrightarrow> ( \<not> ( \<cmnf> \<ls> A ) \<longrightarrow> A = \<cmnf> )" by (rule MMI_syl6ib)
   from S6 S14 show "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cmnf> \<longleftrightarrow> \<not> ( \<cmnf> \<ls> A ) )" by (rule MMI_impbid)
qed

lemma (in MMIsar0) MMI_xrrebndt: 
   shows "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<in> \<real> \<longleftrightarrow> ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) )"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_mnfltt)
   have S2: "A \<in> \<real> \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_ltpnft)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> )" 
     by (rule MMI_jca)
   from S3 have S4: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<in> \<real> \<longrightarrow> ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) )" 
     by (rule MMI_a1i)
   have S5: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cpnf> \<longleftrightarrow> \<not> ( A \<ls> \<cpnf> ) )" 
     by (rule MMI_nltpnftt)
   have S6: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A = \<cmnf> \<longleftrightarrow> \<not> ( \<cmnf> \<ls> A ) )" 
     by (rule MMI_ngtmnftt)
   from S5 S6 have S7: "A \<in> \<real>\<^sup>* \<longrightarrow>   
     ( ( A = \<cpnf> \<or> A = \<cmnf> ) \<longleftrightarrow>   
     ( \<not> ( A \<ls> \<cpnf>) \<or> \<not> ( \<cmnf> \<ls> A ) ) )" by (rule MMI_orbi12d)
   have S8: "\<not> ( ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) ) \<longleftrightarrow>   
     ( \<not> ( \<cmnf> \<ls> A ) \<or> \<not> ( A \<ls> \<cpnf> ) )" by (rule MMI_ianor)
   have S9: "( \<not> ( \<cmnf> \<ls> A ) \<or> \<not> ( A \<ls> \<cpnf> ) ) \<longleftrightarrow>   
     ( \<not> ( A \<ls> \<cpnf> ) \<or> \<not> ( \<cmnf> \<ls> A ) )" by (rule MMI_orcom)
   from S8 S9 have S10: "( \<not> ( A \<ls> \<cpnf> ) \<or> \<not> ( \<cmnf> \<ls> A ) ) \<longleftrightarrow>   
     \<not> ( ( \<cmnf> \<ls> A ) \<and> A \<ls> \<cpnf> )" by (rule MMI_bitr2)
   from S7 S10 have S11: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( ( A = \<cpnf> \<or> A = \<cmnf> ) \<longleftrightarrow>   
 \<not> ( ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) ) )" by (rule MMI_syl6bb)
   from S11 have S12: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) \<longleftrightarrow>   
 \<not> ( ( A = \<cpnf> \<or> A = \<cmnf> ) ) )" by (rule MMI_con2bid)
   have S13: "A \<in> \<real>\<^sup>* \<longleftrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" by (rule MMI_elxr)
   from S13 have S14: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<in> \<real> \<or> A = \<cpnf> \<or> A = \<cmnf> )" by (rule MMI_biimp)
   have S15: "( A \<in> \<real> \<or> A =   
 \<cpnf> \<or> A =   
 \<cmnf> ) \<longleftrightarrow> ( A \<in> \<real> \<or> ( A = \<cpnf> \<or> A = \<cmnf> ) )" by (rule MMI_3orass)
   have S16: "( A \<in> \<real> \<or> ( A = \<cpnf> \<or> A = \<cmnf> ) ) \<longleftrightarrow>   
 ( ( A = \<cpnf> \<or> A = \<cmnf> ) \<or> A \<in> \<real> )" by (rule MMI_orcom)
   from S15 S16 have S17: "( A \<in> \<real> \<or> A =   
 \<cpnf> \<or> A =   
 \<cmnf> ) \<longleftrightarrow> ( ( A = \<cpnf> \<or> A = \<cmnf> ) \<or> A \<in> \<real> )" by (rule MMI_bitr)
   from S14 S17 have S18: "A \<in> \<real>\<^sup>* \<longrightarrow> ( ( A = \<cpnf> \<or> A = \<cmnf> ) \<or> A \<in> \<real> )" by (rule MMI_sylib)
   from S18 have S19: "A \<in> \<real>\<^sup>* \<longrightarrow>   
 ( \<not> ( ( A = \<cpnf> \<or> A = \<cmnf> ) ) \<longrightarrow> A \<in> \<real> )" by (rule MMI_ord)
   from S12 S19 have S20: "A \<in> \<real>\<^sup>* \<longrightarrow> ( ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) \<longrightarrow> A \<in> \<real> )" by (rule MMI_sylbid)
   from S4 S20 show "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<in> \<real> \<longleftrightarrow> ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) )" by (rule MMI_impbid)
qed

lemma (in MMIsar0) MMI_xrret: 
   shows "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> ( \<cmnf> \<ls> A \<and> A \<lsq> B ) ) \<longrightarrow>   
 A \<in> \<real>"
proof -
   have S1: "( \<cmnf> \<ls> A \<and> A \<lsq> B ) \<longrightarrow> \<cmnf> \<ls> A" by (rule MMI_pm3_26)
   from S1 have S2: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> ( \<cmnf> \<ls> A \<and> A \<lsq> B ) ) \<longrightarrow>   
 \<cmnf> \<ls> A" by (rule MMI_adantl)
   have S3: "B \<in> \<real> \<longrightarrow> B \<ls> \<cpnf>" by (rule MMI_ltpnft)
   from S3 have S4: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<longrightarrow> B \<ls> \<cpnf>" by (rule MMI_adantl)
   have S5: "\<cpnf> \<in> \<real>\<^sup>*" by (rule MMI_pnfxr)
   have S6: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* \<and> \<cpnf> \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> \<cpnf> ) \<longrightarrow> A \<ls> \<cpnf> )" by (rule MMI_xrlelttrt)
   from S5 S6 have S7: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real>\<^sup>* ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> \<cpnf> ) \<longrightarrow> A \<ls> \<cpnf> )" by (rule MMI_mp3an3)
   have S8: "B \<in> \<real> \<longrightarrow> B \<in> \<real>\<^sup>*" by (rule MMI_rexrt)
   from S7 S8 have S9: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<longrightarrow>   
 ( ( A \<lsq> B \<and> B \<ls> \<cpnf> ) \<longrightarrow> A \<ls> \<cpnf> )" by (rule MMI_sylan2)
   from S4 S9 have S10: "( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<longrightarrow> ( A \<lsq> B \<longrightarrow> A \<ls> \<cpnf> )" by (rule MMI_mpan2d)
   from S10 have S11: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> A \<lsq> B ) \<longrightarrow> A \<ls> \<cpnf>" by (rule MMI_imp)
   from S11 have S12: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> ( \<cmnf> \<ls> A \<and> A \<lsq> B ) ) \<longrightarrow>   
 A \<ls> \<cpnf>" by (rule MMI_adantrl)
   from S2 S12 have S13: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> ( \<cmnf> \<ls> A \<and> A \<lsq> B ) ) \<longrightarrow>   
 ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> )" by (rule MMI_jca)
   have S14: "A \<in> \<real>\<^sup>* \<longrightarrow> ( A \<in> \<real> \<longleftrightarrow> ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) )" by (rule MMI_xrrebndt)
   from S14 have S15: "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> ( \<cmnf> \<ls> A \<and> A \<lsq> B ) ) \<longrightarrow>   
 ( A \<in> \<real> \<longleftrightarrow> ( \<cmnf> \<ls> A \<and> A \<ls> \<cpnf> ) )" by (rule MMI_ad2antrr)
   from S13 S15 show "( ( A \<in> \<real>\<^sup>* \<and> B \<in> \<real> ) \<and> ( \<cmnf> \<ls> A \<and> A \<lsq> B ) ) \<longrightarrow>   
 A \<in> \<real>" by (rule MMI_mpbird)
qed

lemma (in MMIsar0) MMI_eqlet: 
   shows "( A \<in> \<real> \<and> A = B ) \<longrightarrow> A \<lsq> B"
proof -
   have S1: "A = B \<longrightarrow> ( A \<lsq> A \<longleftrightarrow> A \<lsq> B )" by (rule MMI_breq2)
   from S1 have S2: "( A \<lsq> A \<and> A = B ) \<longrightarrow> A \<lsq> B" by (rule MMI_biimpac)
   have S3: "A \<in> \<real> \<longrightarrow> A \<lsq> A" by (rule MMI_leidt)
   from S2 S3 show "( A \<in> \<real> \<and> A = B ) \<longrightarrow> A \<lsq> B" by (rule MMI_sylan)
qed

lemma (in MMIsar0) MMI_lttri2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<not> ( A = B ) \<longleftrightarrow> ( A \<ls> B \<or> B \<ls> A )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( \<not> ( A = B ) \<longleftrightarrow> ( A \<ls> B \<or> B \<ls> A ) )" by (rule MMI_lttri2t)
   from S1 S2 S3 show "\<not> ( A = B ) \<longleftrightarrow> ( A \<ls> B \<or> B \<ls> A )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_lttri3: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) ) )" by (rule MMI_lttri3t)
   from S1 S2 S3 show "A = B \<longleftrightarrow> ( \<not> ( A \<ls> B ) \<and> \<not> ( B \<ls> A ) )" 
     by (rule MMI_mp2an)
qed

(*****************290-300*****************************)
lemma (in MMIsar0) MMI_letri3: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A ) )" by (rule MMI_letri3t)
   from S1 S2 S3 show "A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_leloe: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B ) )" by (rule MMI_leloet)
   from S1 S2 S3 show "A \<lsq> B \<longleftrightarrow> ( A \<ls> B \<or> A = B )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_ltlen: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<ls> B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A = B ) )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A = B ) ) )" by (rule MMI_ltlent)
   from S1 S2 S3 show "A \<ls> B \<longleftrightarrow> ( A \<lsq> B \<and> \<not> ( A = B ) )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_ltnsym: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<ls> B \<longrightarrow> \<not> ( B \<ls> A )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_ltnsymt)
   from S1 S2 S3 show "A \<ls> B \<longrightarrow> \<not> ( B \<ls> A )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_lenlt: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A ) )" by (rule MMI_lenltt)
   from S1 S2 S3 show "A \<lsq> B \<longleftrightarrow> \<not> ( B \<ls> A )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_ltnle: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<ls> B \<longleftrightarrow> \<not> ( B \<lsq> A )"
proof -
   from A2 have S1: "B \<in> \<real>".
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "B \<lsq> A \<longleftrightarrow> \<not> ( A \<ls> B )" by (rule MMI_lenlt)
   from S3 show "A \<ls> B \<longleftrightarrow> \<not> ( B \<lsq> A )" by (rule MMI_con2bii)
qed

lemma (in MMIsar0) MMI_ltle: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<ls> B \<longrightarrow> A \<lsq> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ls> B \<longrightarrow> A \<lsq> B )" 
     by (rule MMI_ltlet)
   from S1 S2 S3 show "A \<ls> B \<longrightarrow> A \<lsq> B" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_ltlei: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "A \<ls> B"   
   shows "A \<lsq> B"
proof -
   from A3 have S1: "A \<ls> B".
   from A1 have S2: "A \<in> \<real>".
   from A2 have S3: "B \<in> \<real>".
   from S2 S3 have S4: "A \<ls> B \<longrightarrow> A \<lsq> B" by (rule MMI_ltle)
   from S1 S4 show "A \<lsq> B" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_eqle: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A = B \<longrightarrow> A \<lsq> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "A = B \<longleftrightarrow> ( A \<lsq> B \<and> B \<lsq> A )" 
     by (rule MMI_letri3)
   from S3 show "A = B \<longrightarrow> A \<lsq> B" by (rule MMI_pm3_26bd)
qed

lemma (in MMIsar0) MMI_ltne: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A \<ls> B \<longrightarrow> \<not> ( A = B )"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow>   
 ( A \<ls> B \<longrightarrow> \<not> ( A = B ) )" by (rule MMI_ltnet)
   from S1 S2 S3 show "A \<ls> B \<longrightarrow> \<not> ( A = B )" by (rule MMI_mp2an)
qed

(*********** 301, 302 ******************************)

lemma (in MMIsar0) MMI_letri: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A\<lsq>B \<or> B\<lsq>A"
proof -
   from A2 have S1: "B \<in> \<real>".
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "B\<ls>A \<longleftrightarrow> \<not>(A\<lsq>B)" by (rule MMI_ltnle)
   from A2 have S4: "B \<in> \<real>".
   from A1 have S5: "A \<in> \<real>".
   from S4 S5 have S6: "B\<ls>A \<longrightarrow> B\<lsq>A" by (rule MMI_ltle)
   from S3 S6 have S7: "\<not>(A\<lsq>B) \<longrightarrow> B\<lsq>A" by (rule MMI_sylbir)
   from S7 show "A\<lsq>B \<or> B\<lsq>A" by (rule MMI_orri)
qed

lemma (in MMIsar0) MMI_lttr: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<ls>B \<and> B\<ls>C \<longrightarrow> A\<ls>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<ls>B \<and> B\<ls>C \<longrightarrow> A\<ls>C" by (rule MMI_axlttrn)
   from S1 S2 S3 S4 show "A\<ls>B \<and> B\<ls>C \<longrightarrow> A\<ls>C" by (rule MMI_mp3an)
qed

(********* 303 - 305 **********************************)

lemma (in MMIsar0) MMI_lelttr: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<lsq>B \<and> B\<ls>C \<longrightarrow> A\<ls>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<lsq>B \<and> B\<ls>C \<longrightarrow> A\<ls>C" by (rule MMI_lelttrt)
   from S1 S2 S3 S4 show "A\<lsq>B \<and> B\<ls>C \<longrightarrow> A\<ls>C" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_ltletr: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<ls>B \<and> B\<lsq>C \<longrightarrow> A\<ls>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<ls>B \<and> B\<lsq>C \<longrightarrow> A\<ls>C" by (rule MMI_ltletrt)
   from S1 S2 S3 S4 show "A\<ls>B \<and> B\<lsq>C \<longrightarrow> A\<ls>C" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_letr: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<lsq>B \<and> B\<lsq>C \<longrightarrow> A\<lsq>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<and> B\<lsq>C \<longrightarrow> A\<lsq>C" by (rule MMI_letrt)
   from S1 S2 S3 S4 show "A\<lsq>B \<and> B\<lsq>C \<longrightarrow> A\<lsq>C" by (rule MMI_mp3an)
qed

(********** 306 - 310 *************************)

lemma (in MMIsar0) MMI_le2tri3: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longleftrightarrow> A = B \<and> B = C \<and> C = A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "A = B \<longleftrightarrow> A\<lsq>B \<and> B\<lsq>A" by (rule MMI_letri3)
   from S3 have S4: "A\<lsq>B \<and> B\<lsq>A \<longrightarrow> A = B" by (rule MMI_biimpr)
   from A2 have S5: "B \<in> \<real>".
   from A3 have S6: "C \<in> \<real>".
   from A1 have S7: "A \<in> \<real>".
   from S5 S6 S7 have S8: "B\<lsq>C \<and> C\<lsq>A \<longrightarrow> B\<lsq>A" by (rule MMI_letr)
   from S4 S8 have S9: "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longrightarrow> A = B" by (rule MMI_sylan2)
   from S9 have S10: "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longrightarrow> A = B" by (rule MMI_3impb)
   from A2 have S11: "B \<in> \<real>".
   from A3 have S12: "C \<in> \<real>".
   from S11 S12 have S13: "B = C \<longleftrightarrow> B\<lsq>C \<and> C\<lsq>B" by (rule MMI_letri3)
   from S13 have S14: "B\<lsq>C \<and> C\<lsq>B \<longrightarrow> B = C" by (rule MMI_biimpr)
   from A3 have S15: "C \<in> \<real>".
   from A1 have S16: "A \<in> \<real>".
   from A2 have S17: "B \<in> \<real>".
   from S15 S16 S17 have S18: "C\<lsq>A \<and> A\<lsq>B \<longrightarrow> C\<lsq>B" by (rule MMI_letr)
   from S14 S18 have S19: "B\<lsq>C \<and> C\<lsq>A \<and> A\<lsq>B \<longrightarrow> B = C" by (rule MMI_sylan2)
   from S19 have S20: "B\<lsq>C \<and> C\<lsq>A \<and> A\<lsq>B \<longrightarrow> B = C" by (rule MMI_3impb)
   from S20 have S21: "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longrightarrow> B = C" by (rule MMI_3comr)
   from A1 have S22: "A \<in> \<real>".
   from A3 have S23: "C \<in> \<real>".
   from S22 S23 have S24: "A = C \<longleftrightarrow> A\<lsq>C \<and> C\<lsq>A" by (rule MMI_letri3)
   from S24 have S25: "A\<lsq>C \<and> C\<lsq>A \<longrightarrow> A = C" by (rule MMI_biimpr)
   from S25 have S26: "A\<lsq>C \<and> C\<lsq>A \<longrightarrow> C = A" by (rule MMI_eqcomd)
   from A1 have S27: "A \<in> \<real>".
   from A2 have S28: "B \<in> \<real>".
   from A3 have S29: "C \<in> \<real>".
   from S27 S28 S29 have S30: "A\<lsq>B \<and> B\<lsq>C \<longrightarrow> A\<lsq>C" by (rule MMI_letr)
   from S26 S30 have S31: "( A\<lsq>B \<and> B\<lsq>C ) \<and> C\<lsq>A \<longrightarrow> C = A" by (rule MMI_sylan)
   from S31 have S32: "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longrightarrow> C = A" by (rule MMI_3impa)
   from S10 S21 S32 have S33: "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longrightarrow> A = B \<and> B = C \<and> C = A" 
     by (rule MMI_3jca)
   from A1 have S34: "A \<in> \<real>".
   from A2 have S35: "B \<in> \<real>".
   from S34 S35 have S36: "A = B \<longrightarrow> A\<lsq>B" by (rule MMI_eqle)
   from A2 have S37: "B \<in> \<real>".
   from A3 have S38: "C \<in> \<real>".
   from S37 S38 have S39: "B = C \<longrightarrow> B\<lsq>C" by (rule MMI_eqle)
   from A3 have S40: "C \<in> \<real>".
   from A1 have S41: "A \<in> \<real>".
   from S40 S41 have S42: "C = A \<longrightarrow> C\<lsq>A" by (rule MMI_eqle)
   from S36 S39 S42 have S43: "A = B \<and> B = C \<and> C = A \<longrightarrow> A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A" 
     by (rule MMI_3anim123i)
   from S33 S43 show "A\<lsq>B \<and> B\<lsq>C \<and> C\<lsq>A \<longleftrightarrow> A = B \<and> B = C \<and> C = A" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_ltadd2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<ls>B \<longleftrightarrow> C \<ca> A\<ls>C \<ca> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<ls>B \<longrightarrow> C \<ca> A\<ls>C \<ca> B" by (rule MMI_axltadd)
   from S1 S2 S3 S4 have S5: "A\<ls>B \<longrightarrow> C \<ca> A\<ls>C \<ca> B" by (rule MMI_mp3an)
   from A3 have S6: "C \<in> \<real>".
   from A1 have S7: "A \<in> \<real>".
   from S6 S7 have S8: "C \<ca> A \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S9: "C \<in> \<real>".
   from A2 have S10: "B \<in> \<real>".
   from S9 S10 have S11: "C \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S12: "C \<in> \<real>".
   from S12 have S13: "(\<cn>C) \<in> \<real>" by (rule MMI_renegcl)
   have S14: "C \<ca> A \<in> \<real> \<and> C \<ca> B \<in> \<real> \<and> ( (\<cn>C) \<in> \<real>) \<longrightarrow> 
   C \<ca> A\<ls>C \<ca> B \<longrightarrow> (\<cn>C) \<ca> (C \<ca> A) \<ls> (\<cn>C) \<ca> (C \<ca> B)" 
     by (rule MMI_axltadd)
   from S8 S11 S13 S14 have S15: 
     "C \<ca> A\<ls>C \<ca> B \<longrightarrow> (\<cn>C) \<ca> (C \<ca> A) \<ls>(\<cn>C) \<ca> (C \<ca> B)" 
     by (rule MMI_mp3an)
   from S13 have S16: "(\<cn>C) \<in> \<real>" .
   from S16 have S17: "(\<cn>C) \<in> \<complex>" by (rule MMI_recn)
   from A3 have S18: "C \<in> \<real>".
   from S18 have S19: "C \<in> \<complex>" by (rule MMI_recn)
   from S17 S19 have S20: "(\<cn>C) \<ca> C = C \<ca> (\<cn>C)" by (rule MMI_addcom)
   from S19 have S21: "C \<in> \<complex>" .
   from S21 have S22: "C \<ca> (\<cn>C) = \<zero>" by (rule MMI_negid)
   from S20 S22 have S23: "(\<cn>C) \<ca> C = \<zero>" by (rule MMI_eqtr)
   from S23 have S24: "(\<cn>C) \<ca> C \<ca> A = \<zero> \<ca> A" by (rule MMI_opreq1i)
   from S17 have S25: "(\<cn>C) \<in> \<complex>" .
   from S19 have S26: "C \<in> \<complex>" .
   from A1 have S27: "A \<in> \<real>".
   from S27 have S28: "A \<in> \<complex>" by (rule MMI_recn)
   from S25 S26 S28 have S29: "( (\<cn>C) \<ca> C ) \<ca> A = (\<cn>C) \<ca> (C \<ca> A)" 
     by (rule MMI_addass)
   from S28 have S30: "A \<in> \<complex>" .
   from S30 have S31: "\<zero> \<ca> A = A" by (rule MMI_addid2)
   from S24 S29 S31 have S32: "(\<cn>C) \<ca> ( C  \<ca> A ) = A" by (rule MMI_3eqtr3)
   from S23 have S33: "(\<cn>C) \<ca> C = \<zero>" .
   from S33 have S34: "(\<cn>C) \<ca> C \<ca> B = \<zero> \<ca> B" by (rule MMI_opreq1i)
   from S17 have S35: "(\<cn>C) \<in> \<complex>" .
   from S19 have S36: "C \<in> \<complex>" .
   from A2 have S37: "B \<in> \<real>".
   from S37 have S38: "B \<in> \<complex>" by (rule MMI_recn)
   from S35 S36 S38 have S39: "(\<cn>C) \<ca> C \<ca> B = (\<cn>C) \<ca> ( C  \<ca> B)" 
     by (rule MMI_addass)
   from S38 have S40: "B \<in> \<complex>" .
   from S40 have S41: "\<zero> \<ca> B = B" by (rule MMI_addid2)
   from S34 S39 S41 have S42: "(\<cn>C) \<ca> ( C \<ca> B) = B" by (rule MMI_3eqtr3)
   from S15 S32 S42 have S43: "C \<ca> A\<ls>C \<ca> B \<longrightarrow> A\<ls>B" by (rule MMI_3brtr3g)
   from S5 S43 show "A\<ls>B \<longleftrightarrow> C \<ca> A\<ls>C \<ca> B" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_ltadd1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<ls>B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from S1 S2 S3 have S4: "A\<ls>B \<longleftrightarrow> C \<ca> A\<ls>C \<ca> B" by (rule MMI_ltadd2)
   from A3 have S5: "C \<in> \<real>".
   from S5 have S6: "C \<in> \<complex>" by (rule MMI_recn)
   from A1 have S7: "A \<in> \<real>".
   from S7 have S8: "A \<in> \<complex>" by (rule MMI_recn)
   from S6 S8 have S9: "C \<ca> A = A \<ca> C" by (rule MMI_addcom)
   from S6 have S10: "C \<in> \<complex>" .
   from A2 have S11: "B \<in> \<real>".
   from S11 have S12: "B \<in> \<complex>" by (rule MMI_recn)
   from S10 S12 have S13: "C \<ca> B = B \<ca> C" by (rule MMI_addcom)
   from S9 S13 have S14: "C \<ca> A\<ls>C \<ca> B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C" by (rule MMI_breq12i)
   from S4 S14 show "A\<ls>B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C" by (rule MMI_bitr)
qed

lemma (in MMIsar0) MMI_leadd1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C"
proof -
   from A2 have S1: "B \<in> \<real>".
   from A1 have S2: "A \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from S1 S2 S3 have S4: "B\<ls>A \<longleftrightarrow> B \<ca> C\<ls>A \<ca> C" by (rule MMI_ltadd1)
   from S4 have S5: "\<not>(B\<ls>A) \<longleftrightarrow> \<not>(B \<ca> C\<ls>A \<ca> C)" by (rule MMI_negbii)
   from A1 have S6: "A \<in> \<real>".
   from A2 have S7: "B \<in> \<real>".
   from S6 S7 have S8: "A\<lsq>B \<longleftrightarrow> \<not>(B\<ls>A)" by (rule MMI_lenlt)
   from A1 have S9: "A \<in> \<real>".
   from A3 have S10: "C \<in> \<real>".
   from S9 S10 have S11: "A \<ca> C \<in> \<real>" by (rule MMI_readdcl)
   from A2 have S12: "B \<in> \<real>".
   from A3 have S13: "C \<in> \<real>".
   from S12 S13 have S14: "B \<ca> C \<in> \<real>" by (rule MMI_readdcl)
   from S11 S14 have S15: "A \<ca> C\<lsq>B \<ca> C \<longleftrightarrow> \<not>(B \<ca> C\<ls>A \<ca> C)" by (rule MMI_lenlt)
   from S5 S8 S15 show "A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C" by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_leadd2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A\<lsq>B \<longleftrightarrow> C \<ca> A\<lsq>C \<ca> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from S1 S2 S3 have S4: "A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C" by (rule MMI_leadd1)
   from A1 have S5: "A \<in> \<real>".
   from S5 have S6: "A \<in> \<complex>" by (rule MMI_recn)
   from A3 have S7: "C \<in> \<real>".
   from S7 have S8: "C \<in> \<complex>" by (rule MMI_recn)
   from S6 S8 have S9: "A \<ca> C = C \<ca> A" by (rule MMI_addcom)
   from A2 have S10: "B \<in> \<real>".
   from S10 have S11: "B \<in> \<complex>" by (rule MMI_recn)
   from S8 have S12: "C \<in> \<complex>" .
   from S11 S12 have S13: "B \<ca> C = C \<ca> B" by (rule MMI_addcom)
   from S9 S13 have S14: "A \<ca> C\<lsq>B \<ca> C \<longleftrightarrow> C \<ca> A\<lsq>C \<ca> B" by (rule MMI_breq12i)
   from S4 S14 show "A\<lsq>B \<longleftrightarrow> C \<ca> A\<lsq>C \<ca> B" by (rule MMI_bitr)
qed

(******** 311-315 **********************************)


lemma (in MMIsar0) MMI_ltsubadd: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S2 have S3: "(\<cn>B) \<in> \<real>" by (rule MMI_renegcl)
   from S1 S3 have S4: "A \<ca> (\<cn>B) \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S5: "C \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from S4 S5 S6 have S7: "A \<ca> (\<cn>B)\<ls>C \<longleftrightarrow> 
   A \<ca> (\<cn>B) \<ca> B\<ls>C \<ca> B" by (rule MMI_ltadd1)
   from A1 have S8: "A \<in> \<real>".
   from S8 have S9: "A \<in> \<complex>" by (rule MMI_recn)
   from A2 have S10: "B \<in> \<real>".
   from S10 have S11: "B \<in> \<complex>" by (rule MMI_recn)
   from S9 S11 have S12: "A \<ca> (\<cn>B) = A \<cs> B" by (rule MMI_negsub)
   from S12 have S13: "A \<ca> (\<cn>B)\<ls>C \<longleftrightarrow> A \<cs> B\<ls>C" by (rule MMI_breq1i)
   from S9 have S14: "A \<in> \<complex>" .
   from S3 have S15: "(\<cn>B) \<in> \<real>" .
   from S15 have S16: "(\<cn>B) \<in> \<complex>" by (rule MMI_recn)
   from S11 have S17: "B \<in> \<complex>" .
   from S14 S16 S17 have S18: "A \<ca> (\<cn>B) \<ca> B = A \<ca> ((\<cn>B) \<ca> B)" by (rule MMI_addass)
   from S16 have S19: "(\<cn>B) \<in> \<complex>" .
   from S11 have S20: "B \<in> \<complex>" .
   from S19 S20 have S21: "(\<cn>B) \<ca> B = B \<ca> (\<cn>B)" by (rule MMI_addcom)
   from S11 have S22: "B \<in> \<complex>" .
   from S22 have S23: "B \<ca> (\<cn>B) = \<zero>" by (rule MMI_negid)
   from S21 S23 have S24: "(\<cn>B) \<ca> B = \<zero>" by (rule MMI_eqtr)
   from S24 have S25: "A \<ca> ((\<cn>B) \<ca> B) = A \<ca> \<zero>" by (rule MMI_opreq2i)
   from S9 have S26: "A \<in> \<complex>" .
   from S26 have S27: "A \<ca> \<zero> = A" by (rule MMI_addid1)
   from S18 S25 S27 have S28: "A \<ca> (\<cn>B) \<ca> B = A" by (rule MMI_3eqtr)
   from S28 have S29: "A \<ca> (\<cn>B) \<ca> B\<ls>C \<ca> B \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_breq1i)
   from S7 S13 S29 show "A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_3bitr3)
qed

lemma (in MMIsar0) MMI_lesubadd: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from S1 S2 S3 have S4: "A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_ltsubadd)
   from A1 have S5: "A \<in> \<real>".
   from S5 have S6: "A \<in> \<complex>" by (rule MMI_recn)
   from A2 have S7: "B \<in> \<real>".
   from S7 have S8: "B \<in> \<complex>" by (rule MMI_recn)
   from A3 have S9: "C \<in> \<real>".
   from S9 have S10: "C \<in> \<complex>" by (rule MMI_recn)
   from S6 S8 S10 have S11: "A \<cs> B = C \<longleftrightarrow> B \<ca> C = A" by (rule MMI_subadd)
   from S8 have S12: "B \<in> \<complex>" .
   from S10 have S13: "C \<in> \<complex>" .
   from S12 S13 have S14: "B \<ca> C = C \<ca> B" by (rule MMI_addcom)
   from S14 have S15: "B \<ca> C = A \<longleftrightarrow> C \<ca> B = A" by (rule MMI_eqeq1i)
   have S16: "C \<ca> B = A \<longleftrightarrow> A = C \<ca> B" by (rule MMI_eqcom)
   from S11 S15 S16 have S17: "A \<cs> B = C \<longleftrightarrow> A = C \<ca> B" by (rule MMI_3bitr)
   from S4 S17 have S18: "A \<cs> B\<ls>C \<or> A \<cs> B = C \<longleftrightarrow> 
   A\<ls>C \<ca> B \<or> A = C \<ca> B" by (rule MMI_orbi12i_orig)
   from A1 have S19: "A \<in> \<real>".
   from A2 have S20: "B \<in> \<real>".
   from S19 S20 have S21: "A \<cs> B \<in> \<real>" by (rule MMI_resubcl)
   from A3 have S22: "C \<in> \<real>".
   from S21 S22 have S23: "A \<cs> B\<lsq>C \<longleftrightarrow> 
   A \<cs> B\<ls>C \<or> A \<cs> B = C" by (rule MMI_leloe)
   from A1 have S24: "A \<in> \<real>".
   from A3 have S25: "C \<in> \<real>".
   from A2 have S26: "B \<in> \<real>".
   from S25 S26 have S27: "C \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from S24 S27 have S28: "A\<lsq>C \<ca> B \<longleftrightarrow> 
   A\<ls>C \<ca> B \<or> A = C \<ca> B" by (rule MMI_leloe)
   from S18 S23 S28 show "A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_lt2add: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>" and
    A4: "D \<in> \<real>"   
   shows "A\<ls>C \<and> B\<ls>D \<longrightarrow> A \<ca> B\<ls>C \<ca> D"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "A \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S4: "C \<in> \<real>".
   from A2 have S5: "B \<in> \<real>".
   from S4 S5 have S6: "C \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S7: "C \<in> \<real>".
   from A4 have S8: "D \<in> \<real>".
   from S7 S8 have S9: "C \<ca> D \<in> \<real>" by (rule MMI_readdcl)
   from S3 S6 S9 have S10: "A \<ca> B\<ls>C \<ca> B \<and> C \<ca> B\<ls>C \<ca> D \<longrightarrow> A \<ca> B\<ls>C \<ca> D" by (rule MMI_lttr)
   from A1 have S11: "A \<in> \<real>".
   from A3 have S12: "C \<in> \<real>".
   from A2 have S13: "B \<in> \<real>".
   from S11 S12 S13 have S14: "A\<ls>C \<longleftrightarrow> A \<ca> B\<ls>C \<ca> B" by (rule MMI_ltadd1)
   from A2 have S15: "B \<in> \<real>".
   from A4 have S16: "D \<in> \<real>".
   from A3 have S17: "C \<in> \<real>".
   from S15 S16 S17 have S18: "B\<ls>D \<longleftrightarrow> C \<ca> B\<ls>C \<ca> D" by (rule MMI_ltadd2)
   from S10 S14 S18 show "A\<ls>C \<and> B\<ls>D \<longrightarrow> A \<ca> B\<ls>C \<ca> D" by (rule MMI_syl2anb)
qed

lemma (in MMIsar0) MMI_le2add: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>" and
    A4: "D \<in> \<real>"   
   shows "A\<lsq>C \<and> B\<lsq>D \<longrightarrow> A \<ca> B\<lsq>C \<ca> D"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "A \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S4: "C \<in> \<real>".
   from A2 have S5: "B \<in> \<real>".
   from S4 S5 have S6: "C \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from A3 have S7: "C \<in> \<real>".
   from A4 have S8: "D \<in> \<real>".
   from S7 S8 have S9: "C \<ca> D \<in> \<real>" by (rule MMI_readdcl)
   from S3 S6 S9 have S10: 
     "A \<ca> B\<lsq>C \<ca> B \<and> C \<ca> B\<lsq>C \<ca> D \<longrightarrow> 
     A \<ca> B\<lsq>C \<ca> D" by (rule MMI_letr)
   from A1 have S11: "A \<in> \<real>".
   from A3 have S12: "C \<in> \<real>".
   from A2 have S13: "B \<in> \<real>".
   from S11 S12 S13 have S14: "A\<lsq>C \<longleftrightarrow> A \<ca> B\<lsq>C \<ca> B" by (rule MMI_leadd1)
   from A2 have S15: "B \<in> \<real>".
   from A4 have S16: "D \<in> \<real>".
   from A3 have S17: "C \<in> \<real>".
   from S15 S16 S17 have S18: "B\<lsq>D \<longleftrightarrow> C \<ca> B\<lsq>C \<ca> D" by (rule MMI_leadd2)
   from S10 S14 S18 show "A\<lsq>C \<and> B\<lsq>D \<longrightarrow> A \<ca> B\<lsq>C \<ca> D" by (rule MMI_syl2anb)
qed

lemma (in MMIsar0) MMI_addgt0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S2: "A \<in> \<real>".
   from A1 have S3: "A \<in> \<real>".
   from A2 have S4: "B \<in> \<real>".
   from S3 S4 have S5: "A \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from S1 S2 S5 have S6: "\<zero>\<ls>A \<and> A\<ls>A \<ca> B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_lttr)
   have S7: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S8: "B \<in> \<real>".
   from A1 have S9: "A \<in> \<real>".
   from S7 S8 S9 have S10: "\<zero>\<ls>B \<longleftrightarrow> A \<ca> \<zero>\<ls>A \<ca> B" by (rule MMI_ltadd2)
   from A1 have S11: "A \<in> \<real>".
   from S11 have S12: "A \<in> \<complex>" by (rule MMI_recn)
   from S12 have S13: "A \<ca> \<zero> = A" by (rule MMI_addid1)
   from S13 have S14: "A \<ca> \<zero>\<ls>A \<ca> B \<longleftrightarrow> A\<ls>A \<ca> B" by (rule MMI_breq1i)
   from S10 S14 have S15: "\<zero>\<ls>B \<longleftrightarrow> A\<ls>A \<ca> B" by (rule MMI_bitr)
   from S6 S15 show "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_sylan2b)
qed

(******* 316 - 320 *****************************************)

lemma (in MMIsar0) MMI_addge0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A \<ca> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_addgt0)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from S5 S6 have S7: "A \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   from S4 S7 have S8: "\<zero>\<ls>A \<ca> B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_ltle)
   from S3 S8 have S9: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_syl)
   have S10: "\<zero> = A \<longrightarrow> \<zero> \<ca> B = A \<ca> B" by (rule MMI_opreq1)
   from A2 have S11: "B \<in> \<real>".
   from S11 have S12: "B \<in> \<complex>" by (rule MMI_recn)
   from S12 have S13: "\<zero> \<ca> B = B" by (rule MMI_addid2)
   from S10 S13 have S14: "\<zero> = A \<longrightarrow> B = A \<ca> B" by (rule MMI_syl5eqr)
   from S14 have S15: "\<zero> = A \<longrightarrow> 
   \<zero>\<ls>B \<longleftrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_breq2d)
   from S15 have S16: "\<zero> = A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_biimpa)
   from S8 have S17: "\<zero>\<ls>A \<ca> B \<longrightarrow> \<zero>\<lsq>A \<ca> B" .
   from S16 S17 have S18: "\<zero> = A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_syl)
   have S19: "\<zero> = B \<longrightarrow> A \<ca> \<zero> = A \<ca> B" by (rule MMI_opreq2)
   from A1 have S20: "A \<in> \<real>".
   from S20 have S21: "A \<in> \<complex>" by (rule MMI_recn)
   from S21 have S22: "A \<ca> \<zero> = A" by (rule MMI_addid1)
   from S19 S22 have S23: "\<zero> = B \<longrightarrow> A = A \<ca> B" by (rule MMI_syl5eqr)
   from S23 have S24: "\<zero> = B \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_breq2d)
   from S24 have S25: "\<zero>\<ls>A \<and> \<zero> = B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_biimpac)
   from S8 have S26: "\<zero>\<ls>A \<ca> B \<longrightarrow> \<zero>\<lsq>A \<ca> B" .
   from S25 S26 have S27: "\<zero>\<ls>A \<and> \<zero> = B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_syl)
   have S28: "\<zero> = A \<and> \<zero> = B \<longrightarrow> 
   \<zero> \<ca> \<zero> = A \<ca> B" by (rule MMI_opreq12)
   have S29: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S29 have S30: "\<zero> \<ca> \<zero> = \<zero>" by (rule MMI_addid1)
   from S28 S30 have S31: "\<zero> = A \<and> \<zero> = B \<longrightarrow> \<zero> = A \<ca> B" by (rule MMI_syl5eqr)
   have S32: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S7 have S33: "A \<ca> B \<in> \<real>" .
   from S32 S33 have S34: "\<zero> = A \<ca> B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_eqle)
   from S31 S34 have S35: "\<zero> = A \<and> \<zero> = B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_syl)
   from S9 S18 S27 S35 have S36: "(\<zero>\<ls>A \<or> \<zero> = A) \<and> (\<zero>\<ls>B \<or> \<zero> = B) \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_ccase)
   have S37: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S38: "A \<in> \<real>".
   from S37 S38 have S39: "\<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<ls>A \<or> \<zero> = A" by (rule MMI_leloe)
   have S40: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S41: "B \<in> \<real>".
   from S40 S41 have S42: "\<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<ls>B \<or> \<zero> = B" by (rule MMI_leloe)
   from S36 S39 S42 show "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_syl2anb)
qed

lemma (in MMIsar0) MMI_addgegt0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<lsq>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "\<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<ls>A \<or> \<zero> = A" by (rule MMI_leloe)
   from A1 have S4: "A \<in> \<real>".
   from A2 have S5: "B \<in> \<real>".
   from S4 S5 have S6: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_addgt0)
   from S6 have S7: "\<zero>\<ls>A \<longrightarrow> 
   \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_ex)
   have S8: "\<zero> = A \<longrightarrow> \<zero> \<ca> B = A \<ca> B" by (rule MMI_opreq1)
   from A2 have S9: "B \<in> \<real>".
   from S9 have S10: "B \<in> \<complex>" by (rule MMI_recn)
   from S10 have S11: "\<zero> \<ca> B = B" by (rule MMI_addid2)
   from S8 S11 have S12: "\<zero> = A \<longrightarrow> B = A \<ca> B" by (rule MMI_syl5eqr)
   from S12 have S13: "\<zero> = A \<longrightarrow> 
   \<zero>\<ls>B \<longleftrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_breq2d)
   from S13 have S14: "\<zero> = A \<longrightarrow> 
   \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_biimpd)
   from S7 S14 have S15: "\<zero>\<ls>A \<or> \<zero> = A \<longrightarrow> 
   \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_jaoi)
   from S3 S15 have S16: "\<zero>\<lsq>A \<longrightarrow> 
   \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_sylbi)
   from S16 show "\<zero>\<lsq>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_addgt0i: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero>\<ls>A" and
    A4: "\<zero>\<ls>B"   
   shows "\<zero>\<ls>A \<ca> B"
proof -
   from A3 have S1: "\<zero>\<ls>A".
   from A4 have S2: "\<zero>\<ls>B".
   from A1 have S3: "A \<in> \<real>".
   from A2 have S4: "B \<in> \<real>".
   from S3 S4 have S5: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_addgt0)
   from S1 S2 S5 show "\<zero>\<ls>A \<ca> B" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_add20: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> 
   A \<ca> B = \<zero> \<longleftrightarrow> A = \<zero> \<and> B = \<zero>"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "A \<ca> B \<in> \<real>" by (rule MMI_readdcl)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S3 S4 have S5: "A \<ca> B = \<zero> \<longleftrightarrow> 
   \<not>(A \<ca> B\<ls>\<zero>) \<and> \<not>(\<zero>\<ls>A \<ca> B)" by (rule MMI_lttri3)
   from S5 have S6: "A \<ca> B = \<zero> \<longrightarrow> \<not>(\<zero>\<ls>A \<ca> B)" by (rule MMI_pm3_27bd)
   from A1 have S7: "A \<in> \<real>".
   from A2 have S8: "B \<in> \<real>".
   from S7 S8 have S9: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_addgt0)
   from S6 S9 have S10: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<not>(A \<ca> B = \<zero>)" by (rule MMI_nsyl3)
   from S10 have S11: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> A = \<zero> \<and> B = \<zero>" by (rule MMI_pm2_21d)
   have S12: "\<zero> = A \<longrightarrow> \<zero> \<ca> B = A \<ca> B" by (rule MMI_opreq1)
   from A2 have S13: "B \<in> \<real>".
   from S13 have S14: "B \<in> \<complex>" by (rule MMI_recn)
   from S14 have S15: "\<zero> \<ca> B = B" by (rule MMI_addid2)
   from S12 S15 have S16: "\<zero> = A \<longrightarrow> B = A \<ca> B" by (rule MMI_syl5eqr)
   from S16 have S17: "\<zero> = A \<longrightarrow> 
   B = \<zero> \<longleftrightarrow> A \<ca> B = \<zero>" by (rule MMI_eqeq1d)
   from S17 have S18: "\<zero> = A \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> B = \<zero>" by (rule MMI_biimprd)
   have S19: "\<zero> = A \<longleftrightarrow> A = \<zero>" by (rule MMI_eqcom)
   from S19 have S20: "\<zero> = A \<longrightarrow> A = \<zero>" by (rule MMI_biimp)
   from S18 S20 have S21: "\<zero> = A \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> A = \<zero> \<and> B = \<zero>" by (rule MMI_jctild)
   have S22: "\<zero> = B \<longrightarrow> A \<ca> \<zero> = A \<ca> B" by (rule MMI_opreq2)
   from A1 have S23: "A \<in> \<real>".
   from S23 have S24: "A \<in> \<complex>" by (rule MMI_recn)
   from S24 have S25: "A \<ca> \<zero> = A" by (rule MMI_addid1)
   from S22 S25 have S26: "\<zero> = B \<longrightarrow> A = A \<ca> B" by (rule MMI_syl5eqr)
   from S26 have S27: "\<zero> = B \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> A \<ca> B = \<zero>" by (rule MMI_eqeq1d)
   from S27 have S28: "\<zero> = B \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> A = \<zero>" by (rule MMI_biimprd)
   have S29: "\<zero> = B \<longleftrightarrow> B = \<zero>" by (rule MMI_eqcom)
   from S29 have S30: "\<zero> = B \<longrightarrow> B = \<zero>" by (rule MMI_biimp)
   from S28 S30 have S31: "\<zero> = B \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> A = \<zero> \<and> B = \<zero>" by (rule MMI_jctird)
   from S11 S21 S31 have S32: "(\<zero>\<ls>A \<or> \<zero> = A) \<and> (\<zero>\<ls>B \<or> \<zero> = B) \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> A = \<zero> \<and> B = \<zero>" by (rule MMI_ccase2)
   have S33: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S34: "A \<in> \<real>".
   from S33 S34 have S35: "\<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<ls>A \<or> \<zero> = A" by (rule MMI_leloe)
   have S36: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S37: "B \<in> \<real>".
   from S36 S37 have S38: "\<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<ls>B \<or> \<zero> = B" by (rule MMI_leloe)
   from S32 S35 S38 have S39: "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> 
   A \<ca> B = \<zero> \<longrightarrow> A = \<zero> \<and> B = \<zero>" by (rule MMI_syl2anb)
   have S40: "A = \<zero> \<longrightarrow> A \<ca> B = \<zero> \<ca> B" by (rule MMI_opreq1)
   have S41: "B = \<zero> \<longrightarrow> 
   \<zero> \<ca> B = \<zero> \<ca> \<zero>" by (rule MMI_opreq2)
   have S42: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S42 have S43: "\<zero> \<ca> \<zero> = \<zero>" by (rule MMI_addid1)
   from S41 S43 have S44: "B = \<zero> \<longrightarrow> \<zero> \<ca> B = \<zero>" by (rule MMI_syl6eq)
   from S40 S44 have S45: "A = \<zero> \<and> B = \<zero> \<longrightarrow> A \<ca> B = \<zero>" by (rule MMI_sylan9eq)
   from S45 have S46: "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> 
   A = \<zero> \<and> B = \<zero> \<longrightarrow> A \<ca> B = \<zero>" by (rule MMI_a1i)
   from S39 S46 show "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> 
   A \<ca> B = \<zero> \<longleftrightarrow> A = \<zero> \<and> B = \<zero>" by (rule MMI_impbid)
qed

lemma (in MMIsar0) MMI_ltneg: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A1 have S3: "A \<in> \<real>".
   from S3 have S4: "(\<cn>A) \<in> \<real>" by (rule MMI_renegcl)
   from A2 have S5: "B \<in> \<real>".
   from S5 have S6: "(\<cn>B) \<in> \<real>" by (rule MMI_renegcl)
   from S4 S6 have S7: "(\<cn>A) \<ca> (\<cn>B) \<in> \<real>" by (rule MMI_readdcl)
   from S1 S2 S7 have S8: "A\<ls>B \<longleftrightarrow> 
   A \<ca> ((\<cn>A) \<ca> (\<cn>B))\<ls>B \<ca> ((\<cn>A) \<ca> (\<cn>B))" by (rule MMI_ltadd1)
   from A1 have S9: "A \<in> \<real>".
   from S9 have S10: "A \<in> \<complex>" by (rule MMI_recn)
   from S10 have S11: "A \<ca> (\<cn>A) = \<zero>" by (rule MMI_negid)
   from S11 have S12: "A \<ca> (\<cn>A) \<ca> (\<cn>B) = \<zero> \<ca> (\<cn>B)" by (rule MMI_opreq1i)
   from S10 have S13: "A \<in> \<complex>" .
   from S4 have S14: "(\<cn>A) \<in> \<real>" .
   from S14 have S15: "(\<cn>A) \<in> \<complex>" by (rule MMI_recn)
   from S6 have S16: "(\<cn>B) \<in> \<real>" .
   from S16 have S17: "(\<cn>B) \<in> \<complex>" by (rule MMI_recn)
   from S13 S15 S17 have S18: "A \<ca> (\<cn>A) \<ca> (\<cn>B) = A \<ca> ((\<cn>A) \<ca> (\<cn>B))" by (rule MMI_addass)
   from S17 have S19: "(\<cn>B) \<in> \<complex>" .
   from S19 have S20: "\<zero> \<ca> (\<cn>B) = (\<cn>B)" by (rule MMI_addid2)
   from S12 S18 S20 have S21: "A \<ca> ((\<cn>A) \<ca> (\<cn>B)) = (\<cn>B)" by (rule MMI_3eqtr3)
   from A2 have S22: "B \<in> \<real>".
   from S22 have S23: "B \<in> \<complex>" by (rule MMI_recn)
   from S15 have S24: "(\<cn>A) \<in> \<complex>" .
   from S17 have S25: "(\<cn>B) \<in> \<complex>" .
   from S23 S24 S25 have S26: "B \<ca> ((\<cn>A) \<ca> (\<cn>B)) = (\<cn>A) \<ca> (B \<ca> (\<cn>B))" by (rule MMI_add12)
   from S23 have S27: "B \<in> \<complex>" .
   from S27 have S28: "B \<ca> (\<cn>B) = \<zero>" by (rule MMI_negid)
   from S28 have S29: "(\<cn>A) \<ca> (B \<ca> (\<cn>B)) = (\<cn>A) \<ca> \<zero>" by (rule MMI_opreq2i)
   from S15 have S30: "(\<cn>A) \<in> \<complex>" .
   from S30 have S31: "(\<cn>A) \<ca> \<zero> = (\<cn>A)" by (rule MMI_addid1)
   from S26 S29 S31 have S32: "B \<ca> ((\<cn>A) \<ca> (\<cn>B)) = (\<cn>A)" by (rule MMI_3eqtr)
   from S21 S32 have S33: "A \<ca> ((\<cn>A) \<ca> (\<cn>B))\<ls>B \<ca> ((\<cn>A) \<ca> (\<cn>B)) \<longleftrightarrow> 
     (\<cn>B)\<ls>(\<cn>A)" by (rule MMI_breq12i)
   from S8 S33 show "A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)" by (rule MMI_bitr)
qed

(******** 321 - 330 *****************************)

lemma (in MMIsar0) MMI_leneg: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)" by (rule MMI_ltneg)
   from A2 have S4: "B \<in> \<real>".
   from S4 have S5: "B \<in> \<complex>" by (rule MMI_recn)
   from A1 have S6: "A \<in> \<real>".
   from S6 have S7: "A \<in> \<complex>" by (rule MMI_recn)
   from S5 S7 have S8: "(\<cn>B) = (\<cn>A) \<longleftrightarrow> B = A" by (rule MMI_neg11)
   have S9: "B = A \<longleftrightarrow> A = B" by (rule MMI_eqcom)
   from S8 S9 have S10: "A = B \<longleftrightarrow> (\<cn>B) = (\<cn>A)" by (rule MMI_bitr2)
   from S3 S10 have S11: "A\<ls>B \<or> A = B \<longleftrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<or> (\<cn>B) = (\<cn>A)" by (rule MMI_orbi12i_orig)
   from A1 have S12: "A \<in> \<real>".
   from A2 have S13: "B \<in> \<real>".
   from S12 S13 have S14: "A\<lsq>B \<longleftrightarrow> A\<ls>B \<or> A = B" by (rule MMI_leloe)
   from A2 have S15: "B \<in> \<real>".
   from S15 have S16: "(\<cn>B) \<in> \<real>" by (rule MMI_renegcl)
   from A1 have S17: "A \<in> \<real>".
   from S17 have S18: "(\<cn>A) \<in> \<real>" by (rule MMI_renegcl)
   from S16 S18 have S19: "(\<cn>B)\<lsq>(\<cn>A) \<longleftrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<or> (\<cn>B) = (\<cn>A)" by (rule MMI_leloe)
   from S11 S14 S19 show "A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)" by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_ltnegcon2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A\<ls>(\<cn>B) \<longleftrightarrow> B\<ls>(\<cn>A)"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S2 have S3: "(\<cn>B) \<in> \<real>" by (rule MMI_renegcl)
   from S1 S3 have S4: "A\<ls>(\<cn>B) \<longleftrightarrow> (\<cn>(\<cn>B))\<ls>(\<cn>A)" by (rule MMI_ltneg)
   from A2 have S5: "B \<in> \<real>".
   from S5 have S6: "B \<in> \<complex>" by (rule MMI_recn)
   from S6 have S7: "(\<cn>(\<cn>B)) = B" by (rule MMI_negneg)
   from S7 have S8: "(\<cn>(\<cn>B))\<ls>(\<cn>A) \<longleftrightarrow> B\<ls>(\<cn>A)" by (rule MMI_breq1i)
   from S4 S8 show "A\<ls>(\<cn>B) \<longleftrightarrow> B\<ls>(\<cn>A)" by (rule MMI_bitr)
qed

lemma (in MMIsar0) MMI_mulgt0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A\<cdot>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A\<cdot>B" by (rule MMI_axmulgt0)
   from S1 S2 S3 show "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A\<cdot>B" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_mulge0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A\<cdot>B" by (rule MMI_mulgt0)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from S5 S6 have S7: "A\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   from S4 S7 have S8: "\<zero>\<ls>A\<cdot>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_ltle)
   from S3 S8 have S9: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_syl)
   have S10: "\<zero> = A \<longrightarrow> \<zero>\<cdot>B = A\<cdot>B" by (rule MMI_opreq1)
   from A2 have S11: "B \<in> \<real>".
   from S11 have S12: "B \<in> \<complex>" by (rule MMI_recn)
   from S12 have S13: "\<zero>\<cdot>B = \<zero>" by (rule MMI_mul02)
   from S10 S13 have S14: "\<zero> = A \<longrightarrow> \<zero> = A\<cdot>B" by (rule MMI_syl5eqr)
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S7 have S16: "A\<cdot>B \<in> \<real>" .
   from S15 S16 have S17: "\<zero> = A\<cdot>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_eqle)
   from S14 S17 have S18: "\<zero> = A \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_syl)
   have S19: "\<zero> = B \<longrightarrow> A\<cdot>\<zero> = A\<cdot>B" by (rule MMI_opreq2)
   from A1 have S20: "A \<in> \<real>".
   from S20 have S21: "A \<in> \<complex>" by (rule MMI_recn)
   from S21 have S22: "A\<cdot>\<zero> = \<zero>" by (rule MMI_mul01)
   from S19 S22 have S23: "\<zero> = B \<longrightarrow> \<zero> = A\<cdot>B" by (rule MMI_syl5eqr)
   from S17 have S24: "\<zero> = A\<cdot>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" .
   from S23 S24 have S25: "\<zero> = B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_syl)
   from S9 S18 S25 have S26: "(\<zero>\<ls>A \<or> \<zero> = A) \<and> (\<zero>\<ls>B \<or> \<zero> = B) \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_ccase2)
   have S27: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S28: "A \<in> \<real>".
   from S27 S28 have S29: "\<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<ls>A \<or> \<zero> = A" by (rule MMI_leloe)
   have S30: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S31: "B \<in> \<real>".
   from S30 S31 have S32: "\<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<ls>B \<or> \<zero> = B" by (rule MMI_leloe)
   from S26 S29 S32 show "\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_syl2anb)
qed

lemma (in MMIsar0) MMI_mulgt0i: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero>\<ls>A" and
    A4: "\<zero>\<ls>B"   
   shows "\<zero>\<ls>A\<cdot>B"
proof -
   from A3 have S1: "\<zero>\<ls>A".
   from A4 have S2: "\<zero>\<ls>B".
   from A1 have S3: "A \<in> \<real>".
   from A2 have S4: "B \<in> \<real>".
   from S3 S4 have S5: "\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A\<cdot>B" by (rule MMI_mulgt0)
   from S1 S2 S5 show "\<zero>\<ls>A\<cdot>B" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_ltnr: assumes A1: "A \<in> \<real>"   
   shows "\<not>(A\<ls>A)"
proof -
   from A1 have S1: "A \<in> \<real>".
   have S2: "A \<in> \<real> \<longrightarrow> \<not>(A\<ls>A)" by (rule MMI_ltnrt)
   from S1 S2 show "\<not>(A\<ls>A)" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_leid: assumes A1: "A \<in> \<real>"   
   shows "A\<lsq>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   have S2: "A \<in> \<real> \<longrightarrow> A\<lsq>A" by (rule MMI_leidt)
   from S1 S2 show "A\<lsq>A" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_gt0ne0: assumes A1: "A \<in> \<real>"   
   shows "\<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "\<zero>\<ls>A \<longrightarrow> \<not>(\<zero> = A)" by (rule MMI_ltne)
   have S4: "\<zero> \<noteq> A \<longleftrightarrow> \<not>(\<zero> = A)" by (rule MMI_df_ne)
   from S3 S4 have S5: "\<zero>\<ls>A \<longrightarrow> \<zero> \<noteq> A" by (rule MMI_sylibr)
   have S6: "A \<noteq> \<zero> \<longleftrightarrow> \<zero> \<noteq> A" by (rule MMI_necom)
   from S5 S6 show "\<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_sylibr)
qed

lemma (in MMIsar0) MMI_lesub0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> A = \<zero>"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S2: "A \<in> \<real>".
   from S2 have S3: "(\<cn>A) \<in> \<real>" by (rule MMI_renegcl)
   from A2 have S4: "B \<in> \<real>".
   from S1 S3 S4 have S5: "\<zero>\<lsq>(\<cn>A) \<longleftrightarrow> 
   B \<ca> \<zero>\<lsq>B \<ca> (\<cn>A)" by (rule MMI_leadd2)
   from A1 have S6: "A \<in> \<real>".
   have S7: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S6 S7 have S8: "A\<lsq>\<zero> \<longleftrightarrow> (\<cn>\<zero>)\<lsq>(\<cn>A)" by (rule MMI_leneg)
   have S9: "(\<cn>\<zero>) = \<zero>" by (rule MMI_neg0)
   from S9 have S10: "(\<cn>\<zero>)\<lsq>(\<cn>A) \<longleftrightarrow> \<zero>\<lsq>(\<cn>A)" by (rule MMI_breq1i)
   from S8 S10 have S11: "\<zero>\<lsq>(\<cn>A) \<longleftrightarrow> A\<lsq>\<zero>" by (rule MMI_bitr2)
   from A2 have S12: "B \<in> \<real>".
   from S12 have S13: "B \<in> \<complex>" by (rule MMI_recn)
   from S13 have S14: "B \<ca> \<zero> = B" by (rule MMI_addid1)
   from S13 have S15: "B \<in> \<complex>" .
   from A1 have S16: "A \<in> \<real>".
   from S16 have S17: "A \<in> \<complex>" by (rule MMI_recn)
   from S15 S17 have S18: "B \<ca> (\<cn>A) = B \<cs> A" by (rule MMI_negsub)
   from S14 S18 have S19: "B \<ca> \<zero>\<lsq>B \<ca> (\<cn>A) \<longleftrightarrow> B\<lsq>B \<cs> A" by (rule MMI_breq12i)
   from S5 S11 S19 have S20: "B\<lsq>B \<cs> A \<longleftrightarrow> A\<lsq>\<zero>" by (rule MMI_3bitr3r)
   from S20 have S21: "B\<lsq>B \<cs> A \<and> \<zero>\<lsq>A \<longleftrightarrow> 
   A\<lsq>\<zero> \<and> \<zero>\<lsq>A" by (rule MMI_anbi1i)
   have S22: "\<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> 
   B\<lsq>B \<cs> A \<and> \<zero>\<lsq>A" by (rule MMI_ancom)
   from A1 have S23: "A \<in> \<real>".
   have S24: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S23 S24 have S25: "A = \<zero> \<longleftrightarrow> 
   A\<lsq>\<zero> \<and> \<zero>\<lsq>A" by (rule MMI_letri3)
   from S21 S22 S25 show "\<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> A = \<zero>" by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_msqgt0: assumes A1: "A \<in> \<real>"   
   shows "\<not>(A = \<zero>) \<longrightarrow> \<zero>\<ls>A\<cdot>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   have S2: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S1 S2 have S3: "\<not>(A = \<zero>) \<longleftrightarrow> 
   A\<ls>\<zero> \<or> \<zero>\<ls>A" by (rule MMI_lttri2)
   from A1 have S4: "A \<in> \<real>".
   have S5: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S4 S5 have S6: "A\<ls>\<zero> \<longleftrightarrow> (\<cn>\<zero>)\<ls>(\<cn>A)" by (rule MMI_ltneg)
   have S7: "(\<cn>\<zero>) = \<zero>" by (rule MMI_neg0)
   from S7 have S8: "(\<cn>\<zero>)\<ls>(\<cn>A) \<longleftrightarrow> \<zero>\<ls>(\<cn>A)" by (rule MMI_breq1i)
   from S6 S8 have S9: "A\<ls>\<zero> \<longleftrightarrow> \<zero>\<ls>(\<cn>A)" by (rule MMI_bitr)
   from A1 have S10: "A \<in> \<real>".
   from S10 have S11: "(\<cn>A) \<in> \<real>" by (rule MMI_renegcl)
   from S11 have S12: "(\<cn>A) \<in> \<real>" .
   from S11 S12 have S13: "\<zero>\<ls>(\<cn>A) \<and> \<zero>\<ls>(\<cn>A) \<longrightarrow> 
   \<zero>\<ls>(\<cn>A)\<cdot>(\<cn>A)" by (rule MMI_mulgt0)
   from S13 have S14: "\<zero>\<ls>(\<cn>A) \<longrightarrow> 
   \<zero>\<ls>(\<cn>A)\<cdot>(\<cn>A)" by (rule MMI_anidms)
   from A1 have S15: "A \<in> \<real>".
   from S15 have S16: "A \<in> \<complex>" by (rule MMI_recn)
   from S16 have S17: "A \<in> \<complex>" .
   from S16 S17 have S18: "(\<cn>A)\<cdot>(\<cn>A) = A\<cdot>A" by (rule MMI_mul2neg)
   from S14 S18 have S19: "\<zero>\<ls>(\<cn>A) \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_syl6breq)
   from S9 S19 have S20: "A\<ls>\<zero> \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_sylbi)
   from A1 have S21: "A \<in> \<real>".
   from A1 have S22: "A \<in> \<real>".
   from S21 S22 have S23: "\<zero>\<ls>A \<and> \<zero>\<ls>A \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_mulgt0)
   from S23 have S24: "\<zero>\<ls>A \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_anidms)
   from S20 S24 have S25: "A\<ls>\<zero> \<or> \<zero>\<ls>A \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_jaoi)
   from S3 S25 show "\<not>(A = \<zero>) \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_sylbi)
qed

(******** 331 - 340 ************************)

 lemma (in MMIsar0) MMI_msqge0: assumes A1: "A \<in> \<real>"   
   shows "\<zero>\<lsq>A\<cdot>A"
proof -
   have S1: "A = \<zero> \<longrightarrow> A\<cdot>A = A\<cdot>\<zero>" by (rule MMI_opreq2)
   from A1 have S2: "A \<in> \<real>".
   from S2 have S3: "A \<in> \<complex>" by (rule MMI_recn)
   from S3 have S4: "A\<cdot>\<zero> = \<zero>" by (rule MMI_mul01)
   from S1 S4 have S5: "A = \<zero> \<longrightarrow> \<zero> = A\<cdot>A" by (rule MMI_syl6req)
   have S6: "\<zero> = A\<cdot>A \<longrightarrow> 
   \<zero>\<ls>A\<cdot>A \<or> \<zero> = A\<cdot>A" by (rule MMI_olc)
   from S5 S6 have S7: "A = \<zero> \<longrightarrow> 
   \<zero>\<ls>A\<cdot>A \<or> \<zero> = A\<cdot>A" by (rule MMI_syl)
   have S8: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S9: "A \<in> \<real>".
   from A1 have S10: "A \<in> \<real>".
   from S9 S10 have S11: "A\<cdot>A \<in> \<real>" by (rule MMI_remulcl)
   from S8 S11 have S12: "\<zero>\<lsq>A\<cdot>A \<longleftrightarrow> 
   \<zero>\<ls>A\<cdot>A \<or> \<zero> = A\<cdot>A" by (rule MMI_leloe)
   from S7 S12 have S13: "A = \<zero> \<longrightarrow> \<zero>\<lsq>A\<cdot>A" by (rule MMI_sylibr)
   from A1 have S14: "A \<in> \<real>".
   from S14 have S15: "\<not>(A = \<zero>) \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_msqgt0)
   have S16: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S17: "A\<cdot>A \<in> \<real>" .
   from S16 S17 have S18: "\<zero>\<ls>A\<cdot>A \<longrightarrow> \<zero>\<lsq>A\<cdot>A" by (rule MMI_ltle)
   from S15 S18 have S19: "\<not>(A = \<zero>) \<longrightarrow> \<zero>\<lsq>A\<cdot>A" by (rule MMI_syl)
   from S13 S19 show "\<zero>\<lsq>A\<cdot>A" by (rule MMI_pm2_61i)
qed

lemma (in MMIsar0) MMI_gt0ne0i: assumes A1: "A \<in> \<real>" and
    A2: "\<zero>\<ls>A"   
   shows "A \<noteq> \<zero>"
proof -
   from A2 have S1: "\<zero>\<ls>A".
   from A1 have S2: "A \<in> \<real>".
   from S2 have S3: "\<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from S1 S3 show "A \<noteq> \<zero>" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_gt0ne0t: 
   shows "A \<in> \<real> \<and> \<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<noteq> \<zero> \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) \<noteq> \<zero>" by (rule MMI_neeq1)
   from S1 S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>) \<longleftrightarrow> 
   (\<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<longrightarrow> 
    if(A \<in> \<real>, A, \<zero>) \<noteq> \<zero>)" by (rule MMI_imbi12d)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S4 have S5: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S5 have S6: "\<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<longrightarrow> 
    if(A \<in> \<real>, A, \<zero>) \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from S3 S6 have S7: "A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_dedth)
   from S7 show "A \<in> \<real> \<and> \<zero>\<ls>A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_letrit: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<lsq>B \<or> B\<lsq>A"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   B\<lsq>A \<longleftrightarrow> 
   B\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>B \<or> B\<lsq>A \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<or> B\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_orbi12d)
   have S4: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq1)
   from S4 S5 have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<or> B\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<or> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_orbi12d)
   have S7: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S7 have S8: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S9: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S9 have S10: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S8 S10 have S11: "( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<or> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_letri)
   from S3 S6 S11 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<lsq>B \<or> B\<lsq>A" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_lelttrit: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<lsq>B \<or> B\<ls>A"
proof -
   have S1: "A \<in> \<real> \<and> A = B \<longrightarrow> A\<lsq>B" by (rule MMI_eqlet)
   have S2: "A\<lsq>B \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_orc)
   from S1 S2 have S3: "A \<in> \<real> \<and> A = B \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_syl)
   from S3 have S4: "A \<in> \<real> \<longrightarrow> 
   A = B \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_ex)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A = B \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_adantr)
   have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<not>(A = B) \<longleftrightarrow> A\<ls>B \<or> B\<ls>A" by (rule MMI_lttri2t)
   have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longrightarrow> A\<lsq>B" by (rule MMI_ltlet)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<or> B\<ls>A \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_orim1d)
   from S6 S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<not>(A = B) \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_sylbid)
   from S5 S9 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<lsq>B \<or> B\<ls>A" by (rule MMI_pm2_61d)
qed

lemma (in MMIsar0) MMI_ltadd1t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> C = ( if(A \<in> \<real>, A, \<zero>)) \<ca> C" by (rule MMI_opreq1)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> C\<ls>B \<ca> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>B \<ca> C" by (rule MMI_breq1d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<ls>B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>B \<ca> C" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B \<ca> C = ( if(B \<in> \<real>, B, \<zero>)) \<ca> C" by (rule MMI_opreq1)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>B \<ca> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> C" by (rule MMI_breq2d)
   from S5 S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>B \<ca> C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> C" by (rule MMI_bibi12d)
   have S9: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   have S10: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>)) \<ca> C = ( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   from S9 S10 have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq12d)
   from S11 have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_bibi2d)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S15 have S16: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S14 S16 S18 have S19: "( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_ltadd1)
   from S4 S8 S12 S19 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_ltadd2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> C \<ca> A\<ls>C \<ca> B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> A \<ca> C\<ls>B \<ca> C" by (rule MMI_ltadd1t)
   have S2: "A \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A \<ca> C = C \<ca> A" by (rule MMI_axaddcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<ca> C = C \<ca> A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<ca> C = C \<ca> A" by (rule MMI_3adant2)
   have S7: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_axaddcom)
   have S8: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S4 have S9: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" .
   from S7 S8 S9 have S10: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_syl2an)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_3adant1)
   from S6 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> C\<ls>B \<ca> C \<longleftrightarrow> C \<ca> A\<ls>C \<ca> B" by (rule MMI_breq12d)
   from S1 S12 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> C \<ca> A\<ls>C \<ca> B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_leadd1t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> C = ( if(A \<in> \<real>, A, \<zero>)) \<ca> C" by (rule MMI_opreq1)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> C\<lsq>B \<ca> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>B \<ca> C" by (rule MMI_breq1d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>B \<ca> C" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B \<ca> C = ( if(B \<in> \<real>, B, \<zero>)) \<ca> C" by (rule MMI_opreq1)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>B \<ca> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> C" by (rule MMI_breq2d)
   from S5 S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>B \<ca> C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> C" by (rule MMI_bibi12d)
   have S9: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   have S10: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>)) \<ca> C = ( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   from S9 S10 have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq12d)
   from S11 have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> C\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_bibi2d)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S15 have S16: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S14 S16 S18 have S19: "( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<ca> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_leadd1)
   from S4 S8 S12 S19 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_leadd2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> C \<ca> A\<lsq>C \<ca> B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> A \<ca> C\<lsq>B \<ca> C" by (rule MMI_leadd1t)
   have S2: "A \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A \<ca> C = C \<ca> A" by (rule MMI_axaddcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<ca> C = C \<ca> A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<ca> C = C \<ca> A" by (rule MMI_3adant2)
   have S7: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_axaddcom)
   have S8: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S4 have S9: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" .
   from S7 S8 S9 have S10: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_syl2an)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_3adant1)
   from S6 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> C\<lsq>B \<ca> C \<longleftrightarrow> C \<ca> A\<lsq>C \<ca> B" by (rule MMI_breq12d)
   from S1 S12 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> C \<ca> A\<lsq>C \<ca> B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_addge01t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A\<lsq>A \<ca> B"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A \<ca> \<zero>\<lsq>A \<ca> B" by (rule MMI_leadd2t)
   from S1 S2 have S3: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A \<ca> \<zero>\<lsq>A \<ca> B" by (rule MMI_mp3an1)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A \<ca> \<zero>\<lsq>A \<ca> B" by (rule MMI_ancoms)
   have S5: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S6: "A \<in> \<complex> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_ax0id)
   from S5 S6 have S7: "A \<in> \<real> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_syl)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_adantr)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> \<zero>\<lsq>A \<ca> B \<longleftrightarrow> A\<lsq>A \<ca> B" by (rule MMI_breq1d)
   from S4 S9 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A\<lsq>A \<ca> B" by (rule MMI_bitrd)
qed

(**************** 341 -350 *******************************)

lemma (in MMIsar0) MMI_addge02t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A\<lsq>B \<ca> A"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A\<lsq>A \<ca> B" by (rule MMI_addge01t)
   have S2: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_axaddcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>A \<ca> B \<longleftrightarrow> A\<lsq>B \<ca> A" by (rule MMI_breq2d)
   from S1 S6 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A\<lsq>B \<ca> A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_subge0t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<cs> B \<longleftrightarrow> B\<lsq>A"
proof -
   have S1: "B \<in> \<real> \<and> A \<in> \<real> \<and> (\<cn>B) \<in> \<real> \<longrightarrow> 
   B\<lsq>A \<longleftrightarrow> 
   B \<ca> (\<cn>B)\<lsq>A \<ca> (\<cn>B)" by (rule MMI_leadd1t)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   have S4: "B \<in> \<real> \<longrightarrow> (\<cn>B) \<in> \<real>" by (rule MMI_renegclt)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> (\<cn>B) \<in> \<real>" by (rule MMI_adantl)
   from S1 S2 S3 S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B\<lsq>A \<longleftrightarrow> 
   B \<ca> (\<cn>B)\<lsq>A \<ca> (\<cn>B)" by (rule MMI_syl3anc)
   have S7: "B \<in> \<complex> \<longrightarrow> B \<ca> (\<cn>B) = \<zero>" by (rule MMI_negidt)
   from S7 have S8: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> B \<ca> (\<cn>B) = \<zero>" by (rule MMI_adantl)
   have S9: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> (\<cn>B) = A \<cs> B" by (rule MMI_negsubt)
   from S8 S9 have S10: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> 
   B \<ca> (\<cn>B)\<lsq>A \<ca> (\<cn>B) \<longleftrightarrow> \<zero>\<lsq>A \<cs> B" by (rule MMI_breq12d)
   have S11: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S12: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S10 S11 S12 have S13: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<ca> (\<cn>B)\<lsq>A \<ca> (\<cn>B) \<longleftrightarrow> \<zero>\<lsq>A \<cs> B" by (rule MMI_syl2an)
   from S6 S13 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<cs> B \<longleftrightarrow> B\<lsq>A" by (rule MMI_bitr2d)
qed

lemma (in MMIsar0) MMI_subge0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<lsq>A \<cs> B \<longleftrightarrow> B\<lsq>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<cs> B \<longleftrightarrow> B\<lsq>A" by (rule MMI_subge0t)
   from S1 S2 S3 show "\<zero>\<lsq>A \<cs> B \<longleftrightarrow> B\<lsq>A" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_ltsubaddt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<cs> B = ( if(A \<in> \<real>, A, \<zero>)) \<cs> B" by (rule MMI_opreq1)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<ls>C" by (rule MMI_breq1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<ls>C \<ca> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> B" by (rule MMI_breq1)
   from S2 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> B" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B = ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S5 have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>C" by (rule MMI_breq1d)
   have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   C \<ca> B = C \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S6 S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   have S10: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   C \<ca> ( if(B \<in> \<real>, B, \<zero>)) = ( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq1)
   from S11 have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S10 S12 have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<ca> ( if(B \<in> \<real>, B, \<zero>))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   have S14: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S14 have S15: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S16: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S16 have S17: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S18: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S18 have S19: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S15 S17 S19 have S20: "( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_ltsubadd)
   from S4 S9 S13 S20 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_ltsubadd2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>B \<ca> C"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_ltsubaddt)
   have S2: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_axaddcom)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_3adant1)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<ca> C \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_breq2d)
   from S1 S7 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>B \<ca> C" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_lesubaddt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<cs> B = ( if(A \<in> \<real>, A, \<zero>)) \<cs> B" by (rule MMI_opreq1)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<lsq>C" by (rule MMI_breq1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>C \<ca> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> B" by (rule MMI_breq1)
   from S2 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> B" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B = ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S5 have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C" by (rule MMI_breq1d)
   have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   C \<ca> B = C \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S6 S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<cs> B\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   have S10: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   C \<ca> ( if(B \<in> \<real>, B, \<zero>)) = ( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq1)
   from S11 have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S10 S12 have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<ca> ( if(B \<in> \<real>, B, \<zero>))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   have S14: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S14 have S15: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S16: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S16 have S17: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S18: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S18 have S19: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S15 S17 S19 have S20: "( if(A \<in> \<real>, A, \<zero>)) \<cs> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_lesubadd)
   from S4 S9 S13 S20 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_lesubadd2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>B \<ca> C"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_lesubaddt)
   have S2: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_axaddcom)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<ca> C = C \<ca> B" by (rule MMI_3adant1)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<ca> C \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_breq2d)
   from S1 S7 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>B \<ca> C" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_ltaddsubt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<ls>C \<longleftrightarrow> A\<ls>C \<cs> B"
proof -
   have S1: "C \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<lsq>A \<longleftrightarrow> C\<lsq>A \<ca> B" by (rule MMI_lesubaddt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C \<cs> B\<lsq>A \<longleftrightarrow> C\<lsq>A \<ca> B" by (rule MMI_3com13)
   have S3: "C \<cs> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<lsq>A \<longleftrightarrow> \<not>(A\<ls>C \<cs> B)" by (rule MMI_lenltt)
   have S4: "C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> C \<cs> B \<in> \<real>" by (rule MMI_resubclt)
   from S3 S4 have S5: "(C \<in> \<real> \<and> B \<in> \<real>) \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<lsq>A \<longleftrightarrow> \<not>(A\<ls>C \<cs> B)" by (rule MMI_sylan)
   from S5 have S6: "C \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<lsq>A \<longleftrightarrow> \<not>(A\<ls>C \<cs> B)" by (rule MMI_3impa)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C \<cs> B\<lsq>A \<longleftrightarrow> \<not>(A\<ls>C \<cs> B)" by (rule MMI_3com13)
   have S8: "C \<in> \<real> \<and> A \<ca> B \<in> \<real> \<longrightarrow> 
   C\<lsq>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<ls>C)" by (rule MMI_lenltt)
   have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" by (rule MMI_axaddrcl)
   from S8 S9 have S10: "C \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   C\<lsq>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<ls>C)" by (rule MMI_sylan2)
   from S10 have S11: "C \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   C\<lsq>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<ls>C)" by (rule MMI_3impb)
   from S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C\<lsq>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<ls>C)" by (rule MMI_3coml)
   from S2 S7 S12 have S13: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<not>(A \<ca> B\<ls>C) \<longleftrightarrow> \<not>(A\<ls>C \<cs> B)" by (rule MMI_3bitr3rd)
   from S13 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<ls>C \<longleftrightarrow> A\<ls>C \<cs> B" by (rule MMI_con4bid)
qed

lemma (in MMIsar0) MMI_ltaddsub2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<ls>C \<longleftrightarrow> B\<ls>C \<cs> A"
proof -
   have S1: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_axaddcom)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_syl2an)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_3adant3)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<ls>C \<longleftrightarrow> B \<ca> A\<ls>C" by (rule MMI_breq1d)
   have S7: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<ca> A\<ls>C \<longleftrightarrow> B\<ls>C \<cs> A" by (rule MMI_ltaddsubt)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<ca> A\<ls>C \<longleftrightarrow> B\<ls>C \<cs> A" by (rule MMI_3com12)
   from S6 S8 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<ls>C \<longleftrightarrow> B\<ls>C \<cs> A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_leaddsubt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<cs> B"
proof -
   have S1: "C \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<ls>A \<longleftrightarrow> C\<ls>A \<ca> B" by (rule MMI_ltsubaddt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C \<cs> B\<ls>A \<longleftrightarrow> C\<ls>A \<ca> B" by (rule MMI_3com13)
   have S3: "C \<cs> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<ls>A \<longleftrightarrow> \<not>(A\<lsq>C \<cs> B)" by (rule MMI_ltnlet)
   have S4: "C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> C \<cs> B \<in> \<real>" by (rule MMI_resubclt)
   from S3 S4 have S5: "(C \<in> \<real> \<and> B \<in> \<real>) \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<ls>A \<longleftrightarrow> \<not>(A\<lsq>C \<cs> B)" by (rule MMI_sylan)
   from S5 have S6: "C \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   C \<cs> B\<ls>A \<longleftrightarrow> \<not>(A\<lsq>C \<cs> B)" by (rule MMI_3impa)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C \<cs> B\<ls>A \<longleftrightarrow> \<not>(A\<lsq>C \<cs> B)" by (rule MMI_3com13)
   have S8: "C \<in> \<real> \<and> A \<ca> B \<in> \<real> \<longrightarrow> 
   C\<ls>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<lsq>C)" by (rule MMI_ltnlet)
   have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" by (rule MMI_axaddrcl)
   from S8 S9 have S10: "C \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   C\<ls>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<lsq>C)" by (rule MMI_sylan2)
   from S10 have S11: "C \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   C\<ls>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<lsq>C)" by (rule MMI_3impb)
   from S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C\<ls>A \<ca> B \<longleftrightarrow> \<not>(A \<ca> B\<lsq>C)" by (rule MMI_3coml)
   from S2 S7 S12 have S13: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<not>(A \<ca> B\<lsq>C) \<longleftrightarrow> \<not>(A\<lsq>C \<cs> B)" by (rule MMI_3bitr3rd)
   from S13 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<cs> B" by (rule MMI_con4bid)
qed

(********** 351 - 360 *************************)

lemma (in MMIsar0) MMI_leaddsub2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<lsq>C \<longleftrightarrow> B\<lsq>C \<cs> A"
proof -
   have S1: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_axaddcom)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_syl2an)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_3adant3)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<lsq>C \<longleftrightarrow> B \<ca> A\<lsq>C" by (rule MMI_breq1d)
   have S7: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<ca> A\<lsq>C \<longleftrightarrow> B\<lsq>C \<cs> A" by (rule MMI_leaddsubt)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<ca> A\<lsq>C \<longleftrightarrow> B\<lsq>C \<cs> A" by (rule MMI_3com12)
   from S6 S8 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<lsq>C \<longleftrightarrow> B\<lsq>C \<cs> A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_sublet: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A \<cs> C\<lsq>B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_lesubaddt)
   have S2: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<cs> C\<lsq>B \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_lesubadd2t)
   from S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> C\<lsq>B \<longleftrightarrow> A\<lsq>C \<ca> B" by (rule MMI_3com23)
   from S1 S3 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A \<cs> C\<lsq>B" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_lesubt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<cs> C \<longleftrightarrow> C\<lsq>B \<cs> A"
proof -
   have S1: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> C\<lsq>B \<longleftrightarrow> A\<lsq>B \<cs> C" by (rule MMI_leaddsubt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> C\<lsq>B \<longleftrightarrow> A\<lsq>B \<cs> C" by (rule MMI_3com23)
   have S3: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> C\<lsq>B \<longleftrightarrow> C\<lsq>B \<cs> A" by (rule MMI_leaddsub2t)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> C\<lsq>B \<longleftrightarrow> C\<lsq>B \<cs> A" by (rule MMI_3com23)
   from S2 S4 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<cs> C \<longleftrightarrow> C\<lsq>B \<cs> A" by (rule MMI_bitr3d)
qed

lemma (in MMIsar0) MMI_ltsubadd2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>B \<ca> C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>B \<ca> C" by (rule MMI_ltsubadd2t)
   from S1 S2 S3 S4 show "A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>B \<ca> C" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_lesubadd2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>B \<ca> C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>B \<ca> C" by (rule MMI_lesubadd2t)
   from S1 S2 S3 S4 show "A \<cs> B\<lsq>C \<longleftrightarrow> A\<lsq>B \<ca> C" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_ltaddsub: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "A \<ca> B\<ls>C \<longleftrightarrow> A\<ls>C \<cs> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> B\<ls>C \<longleftrightarrow> A\<ls>C \<cs> B" by (rule MMI_ltaddsubt)
   from S1 S2 S3 S4 show "A \<ca> B\<ls>C \<longleftrightarrow> A\<ls>C \<cs> B" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_ltmullem: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero>\<ls>C \<longrightarrow> 
   A\<ls>B \<longrightarrow> A\<cdot>C\<ls>B\<cdot>C"
proof -
   from A2 have S1: "B \<in> \<real>".
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "B \<cs> A \<in> \<real>" by (rule MMI_resubcl)
   from A3 have S4: "C \<in> \<real>".
   from S3 S4 have S5: "\<zero>\<ls>B \<cs> A \<and> \<zero>\<ls>C \<longrightarrow> 
   \<zero>\<ls>(B \<cs> A)\<cdot>C" by (rule MMI_mulgt0)
   from S5 have S6: "\<zero>\<ls>C \<longrightarrow> 
   \<zero>\<ls>B \<cs> A \<longrightarrow> 
   \<zero>\<ls>(B \<cs> A)\<cdot>C" by (rule MMI_expcom)
   from A1 have S7: "A \<in> \<real>".
   from S7 have S8: "A \<in> \<complex>" by (rule MMI_recn)
   from S8 have S9: "\<zero> \<ca> A = A" by (rule MMI_addid2)
   from S9 have S10: "\<zero> \<ca> A\<ls>B \<longleftrightarrow> A\<ls>B" by (rule MMI_breq1i)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S12: "A \<in> \<real>".
   from A2 have S13: "B \<in> \<real>".
   from S11 S12 S13 have S14: "\<zero> \<ca> A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A" by (rule MMI_ltaddsub)
   from S10 S14 have S15: "A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A" by (rule MMI_bitr3)
   from A2 have S16: "B \<in> \<real>".
   from S16 have S17: "B \<in> \<complex>" by (rule MMI_recn)
   from S8 have S18: "A \<in> \<complex>" .
   from A3 have S19: "C \<in> \<real>".
   from S19 have S20: "C \<in> \<complex>" by (rule MMI_recn)
   from S17 S18 S20 have S21: "(B \<cs> A)\<cdot>C = B\<cdot>C \<cs> A\<cdot>C" by (rule MMI_subdir)
   from S21 have S22: "\<zero>\<ls>(B \<cs> A)\<cdot>C \<longleftrightarrow> 
   \<zero>\<ls>B\<cdot>C \<cs> A\<cdot>C" by (rule MMI_breq2i)
   have S23: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S24: "A \<in> \<real>".
   from A3 have S25: "C \<in> \<real>".
   from S24 S25 have S26: "A\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S27: "B \<in> \<real>".
   from A3 have S28: "C \<in> \<real>".
   from S27 S28 have S29: "B\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from S23 S26 S29 have S30: "\<zero> \<ca> A\<cdot>C\<ls>B\<cdot>C \<longleftrightarrow> 
   \<zero>\<ls>B\<cdot>C \<cs> A\<cdot>C" by (rule MMI_ltaddsub)
   from S26 have S31: "A\<cdot>C \<in> \<real>" .
   from S31 have S32: "A\<cdot>C \<in> \<complex>" by (rule MMI_recn)
   from S32 have S33: "\<zero> \<ca> A\<cdot>C = A\<cdot>C" by (rule MMI_addid2)
   from S33 have S34: "\<zero> \<ca> A\<cdot>C\<ls>B\<cdot>C \<longleftrightarrow> A\<cdot>C\<ls>B\<cdot>C" by (rule MMI_breq1i)
   from S22 S30 S34 have S35: "A\<cdot>C\<ls>B\<cdot>C \<longleftrightarrow> 
   \<zero>\<ls>(B \<cs> A)\<cdot>C" by (rule MMI_3bitr2r)
   from S6 S15 S35 show "\<zero>\<ls>C \<longrightarrow> 
   A\<ls>B \<longrightarrow> A\<cdot>C\<ls>B\<cdot>C" by (rule MMI_3imtr4g)
qed

lemma (in MMIsar0) MMI_ltsub23t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A \<cs> C\<ls>B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_ltsubaddt)
   have S2: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<cs> C\<ls>B \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_ltsubadd2t)
   from S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> C\<ls>B \<longleftrightarrow> A\<ls>C \<ca> B" by (rule MMI_3com23)
   from S1 S3 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<cs> B\<ls>C \<longleftrightarrow> A \<cs> C\<ls>B" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_ltsub13t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<cs> C \<longleftrightarrow> C\<ls>B \<cs> A"
proof -
   have S1: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> C\<ls>B \<longleftrightarrow> A\<ls>B \<cs> C" by (rule MMI_ltaddsubt)
   have S2: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> C\<ls>B \<longleftrightarrow> C\<ls>B \<cs> A" by (rule MMI_ltaddsub2t)
   from S1 S2 have S3: "A \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<cs> C \<longleftrightarrow> C\<ls>B \<cs> A" by (rule MMI_bitr3d)
   from S3 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<cs> C \<longleftrightarrow> C\<ls>B \<cs> A" by (rule MMI_3com23)
qed

lemma (in MMIsar0) MMI_lt2addt: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A\<ls>C \<and> B\<ls>D \<longrightarrow> A \<ca> B\<ls>C \<ca> D"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C" by (rule MMI_breq1)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<ls>C \<and> B\<ls>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> B\<ls>D" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_opreq1)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B\<ls>C \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<ls>C \<ca> D" by (rule MMI_breq1d)
   from S2 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<ls>C \<and> B\<ls>D \<longrightarrow> A \<ca> B\<ls>C \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> B\<ls>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<ls>C \<ca> D)" by (rule MMI_imbi12d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<ls>D \<longleftrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<ls>D" by (rule MMI_breq1)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> B\<ls>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D" by (rule MMI_anbi2d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<ls>C \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<ca> D" by (rule MMI_breq1d)
   from S7 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> B\<ls>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<ls>C \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<ca> D)" by (rule MMI_imbi12d)
   have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   from S11 have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D" by (rule MMI_anbi1d)
   have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   C \<ca> D = ( if(C \<in> \<real>, C, \<zero>)) \<ca> D" by (rule MMI_opreq1)
   from S13 have S14: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> D" by (rule MMI_breq2d)
   from S12 S14 have S15: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>C \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> D)" by (rule MMI_imbi12d)
   have S16: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longleftrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_breq2)
   from S16 have S17: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_anbi2d)
   have S18: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(C \<in> \<real>, C, \<zero>)) \<ca> D = ( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_opreq2)
   from S18 have S19: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_breq2d)
   from S17 S19 have S20: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(D \<in> \<real>, D, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>)))" by (rule MMI_imbi12d)
   have S21: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S21 have S22: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S23: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S23 have S24: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S25: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S25 have S26: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S27: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S27 have S28: " if(D \<in> \<real>, D, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S22 S24 S26 S28 have S29: "( if(A \<in> \<real>, A, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(D \<in> \<real>, D, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<ls>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_lt2add)
   from S5 S10 S15 S20 S29 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A\<ls>C \<and> B\<ls>D \<longrightarrow> A \<ca> B\<ls>C \<ca> D" by (rule MMI_dedth4h)
qed

(********** 361 - 370 **********************************)

lemma (in MMIsar0) MMI_le2addt: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A\<lsq>C \<and> B\<lsq>D \<longrightarrow> A \<ca> B\<lsq>C \<ca> D"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C" by (rule MMI_breq1)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>C \<and> B\<lsq>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> B\<lsq>D" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_opreq1)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B\<lsq>C \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<lsq>C \<ca> D" by (rule MMI_breq1d)
   from S2 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<lsq>C \<and> B\<lsq>D \<longrightarrow> A \<ca> B\<lsq>C \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> B\<lsq>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<lsq>C \<ca> D)" by (rule MMI_imbi12d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<lsq>D \<longleftrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<lsq>D" by (rule MMI_breq1)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> B\<lsq>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D" by (rule MMI_anbi2d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<lsq>C \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<ca> D" by (rule MMI_breq1d)
   from S7 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> B\<lsq>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B\<lsq>C \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<ca> D)" by (rule MMI_imbi12d)
   have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   from S11 have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D" by (rule MMI_anbi1d)
   have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   C \<ca> D = ( if(C \<in> \<real>, C, \<zero>)) \<ca> D" by (rule MMI_opreq1)
   from S13 have S14: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> D" by (rule MMI_breq2d)
   from S12 S14 have S15: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>C \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>C \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> D)" by (rule MMI_imbi12d)
   have S16: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longleftrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_breq2)
   from S16 have S17: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_anbi2d)
   have S18: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(C \<in> \<real>, C, \<zero>)) \<ca> D = ( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_opreq2)
   from S18 have S19: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> D \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_breq2d)
   from S17 S19 have S20: "D =  if(D \<in> \<real>, D, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>D \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> D) \<longleftrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(D \<in> \<real>, D, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>)))" by (rule MMI_imbi12d)
   have S21: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S21 have S22: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S23: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S23 have S24: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S25: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S25 have S26: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S27: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S27 have S28: " if(D \<in> \<real>, D, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S22 S24 S26 S28 have S29: "( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(D \<in> \<real>, D, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(C \<in> \<real>, C, \<zero>)) \<ca> ( if(D \<in> \<real>, D, \<zero>))" by (rule MMI_le2add)
   from S5 S10 S15 S20 S29 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A\<lsq>C \<and> B\<lsq>D \<longrightarrow> A \<ca> B\<lsq>C \<ca> D" by (rule MMI_dedth4h)
qed

lemma (in MMIsar0) MMI_addgt0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<ls>A \<and> \<zero>\<ls>B \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_opreq1)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<ls>A \<ca> B \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_breq2d)
   from S2 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B) \<longleftrightarrow> 
   (\<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B)" by (rule MMI_imbi12d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<ls>B \<longleftrightarrow> 
   \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S7 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B) \<longleftrightarrow> 
   (\<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S12 S14 have S15: "\<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_addgt0)
   from S5 S10 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_dedth2h)
   from S16 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<ls>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_addgegt0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<lsq>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<and> \<zero>\<ls>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_opreq1)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<ls>A \<ca> B \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_breq2d)
   from S2 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B) \<longleftrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B)" by (rule MMI_imbi12d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<ls>B \<longleftrightarrow> 
   \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S7 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>B \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> B) \<longleftrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S12 S14 have S15: "\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_addgegt0)
   from S5 S10 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_dedth2h)
   from S16 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<lsq>A \<and> \<zero>\<ls>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_addgtge0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<ls>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<ls>A \<ca> B"
proof -
   have S1: "(B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero>\<lsq>B \<and> \<zero>\<ls>A \<longrightarrow> \<zero>\<ls>B \<ca> A" by (rule MMI_addgegt0t)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longleftrightarrow> 
   B \<in> \<real> \<and> A \<in> \<real>" by (rule MMI_ancom)
   have S3: "\<zero>\<ls>A \<and> \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>B \<and> \<zero>\<ls>A" by (rule MMI_ancom)
   from S1 S2 S3 have S4: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<ls>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<ls>B \<ca> A" by (rule MMI_syl2anb)
   have S5: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_axaddcom)
   have S6: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S7: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S5 S6 S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_syl2an)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<ls>A \<and> \<zero>\<lsq>B \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_adantr)
   from S4 S9 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<ls>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<ls>A \<ca> B" by (rule MMI_breqtrrd)
qed

lemma (in MMIsar0) MMI_addge0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A \<ca> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_opreq1)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<ca> B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> B" by (rule MMI_breq2d)
   from S2 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A \<ca> B) \<longleftrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> B)" by (rule MMI_imbi12d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ca> B = ( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S7 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> B) \<longleftrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S12 S14 have S15: "\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<ca> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_addge0)
   from S5 S10 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_dedth2h)
   from S16 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A \<ca> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltaddpost: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B \<ca> \<zero>\<ls>B \<ca> A" by (rule MMI_ltadd2t)
   from S1 S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B \<ca> \<zero>\<ls>B \<ca> A" by (rule MMI_mp3an1)
   have S4: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S5: "B \<in> \<complex> \<longrightarrow> B \<ca> \<zero> = B" by (rule MMI_ax0id)
   from S4 S5 have S6: "B \<in> \<real> \<longrightarrow> B \<ca> \<zero> = B" by (rule MMI_syl)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<ca> \<zero> = B" by (rule MMI_adantl)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<ca> \<zero>\<ls>B \<ca> A \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_breq1d)
   from S3 S8 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_ltaddpos2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>A \<ca> B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_ltaddpost)
   have S2: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_axaddcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B = B \<ca> A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B\<ls>A \<ca> B \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_breq2d)
   from S1 S6 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>A \<ca> B" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_subge02t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A \<cs> B\<lsq>A"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A\<lsq>A \<ca> B" by (rule MMI_addge01t)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>A \<longleftrightarrow> A\<lsq>A \<ca> B" by (rule MMI_lesubaddt)
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   from S3 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" .
   from S2 S3 S4 S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<cs> B\<lsq>A \<longleftrightarrow> A\<lsq>A \<ca> B" by (rule MMI_syl3anc)
   from S1 S6 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> A \<cs> B\<lsq>A" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_ltsubpost: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B \<cs> A\<ls>B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_ltaddpost)
   have S2: "B \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<cs> A\<ls>B \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_ltsubaddt)
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S3 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" .
   from S2 S3 S4 S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<cs> A\<ls>B \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_syl3anc)
   from S1 S6 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B \<cs> A\<ls>B" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_posdift: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A"
proof -
   have S1: "B \<cs> A \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>B \<cs> A \<longleftrightarrow> A\<ls>A \<ca> (B \<cs> A)" by (rule MMI_ltaddpost)
   have S2: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> B \<cs> A \<in> \<real>" by (rule MMI_resubclt)
   from S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<cs> A \<in> \<real>" by (rule MMI_ancoms)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S1 S3 S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>B \<cs> A \<longleftrightarrow> A\<ls>A \<ca> (B \<cs> A)" by (rule MMI_sylanc)
   have S6: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> (B \<cs> A) = B" by (rule MMI_pncan3t)
   have S7: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S8: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S6 S7 S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> (B \<cs> A) = B" by (rule MMI_syl2an)
   from S9 have S10: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>A \<ca> (B \<cs> A) \<longleftrightarrow> A\<ls>B" by (rule MMI_breq2d)
   from S5 S10 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A" by (rule MMI_bitr2d)
qed

(******** 371 - 380 ********************************)

lemma (in MMIsar0) MMI_ltnegt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<cn>A) = (\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_negeq)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<longleftrightarrow> 
   (\<cn>B)\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_breq2d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>B \<longleftrightarrow> 
   (\<cn>B)\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<cn>B) = (\<cn>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_negeq)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   (\<cn>( if(B \<in> \<real>, B, \<zero>)))\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_breq1d)
   from S5 S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<ls>B \<longleftrightarrow> 
   (\<cn>B)\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>)))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   (\<cn>( if(B \<in> \<real>, B, \<zero>)))\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_bibi12d)
   have S9: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S9 have S10: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S10 S12 have S13: "( if(A \<in> \<real>, A, \<zero>))\<ls>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   (\<cn>( if(B \<in> \<real>, B, \<zero>)))\<ls>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_ltneg)
   from S4 S8 S13 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_ltnegcon1t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>A"
proof -
   have S1: "(\<cn>A) \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>(\<cn>A))" by (rule MMI_ltnegt)
   have S2: "A \<in> \<real> \<longrightarrow> (\<cn>A) \<in> \<real>" by (rule MMI_renegclt)
   from S1 S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>(\<cn>A))" by (rule MMI_sylan)
   have S4: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S5: "A \<in> \<complex> \<longrightarrow> (\<cn>(\<cn>A)) = A" by (rule MMI_negnegt)
   from S4 S5 have S6: "A \<in> \<real> \<longrightarrow> (\<cn>(\<cn>A)) = A" by (rule MMI_syl)
   from S6 have S7: "A \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>B)\<ls>A" by (rule MMI_breq2d)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>B)\<ls>A" by (rule MMI_adantr)
   from S3 S8 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lenegt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<cn>A) = (\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_negeq)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>A) \<longleftrightarrow> 
   (\<cn>B)\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_breq2d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   (\<cn>B)\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<cn>B) = (\<cn>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_negeq)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   (\<cn>( if(B \<in> \<real>, B, \<zero>)))\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_breq1d)
   from S5 S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<lsq>B \<longleftrightarrow> 
   (\<cn>B)\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>)))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   (\<cn>( if(B \<in> \<real>, B, \<zero>)))\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_bibi12d)
   have S9: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S9 have S10: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S10 S12 have S13: "( if(A \<in> \<real>, A, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   (\<cn>( if(B \<in> \<real>, B, \<zero>)))\<lsq>(\<cn>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_leneg)
   from S4 S8 S13 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_lenegcon1t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>A"
proof -
   have S1: "(\<cn>A) \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>(\<cn>A))" by (rule MMI_lenegt)
   have S2: "A \<in> \<real> \<longrightarrow> (\<cn>A) \<in> \<real>" by (rule MMI_renegclt)
   from S1 S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>(\<cn>A))" by (rule MMI_sylan)
   have S4: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S5: "A \<in> \<complex> \<longrightarrow> (\<cn>(\<cn>A)) = A" by (rule MMI_negnegt)
   from S4 S5 have S6: "A \<in> \<real> \<longrightarrow> (\<cn>(\<cn>A)) = A" by (rule MMI_syl)
   from S6 have S7: "A \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>B)\<lsq>A" by (rule MMI_breq2d)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>B)\<lsq>A" by (rule MMI_adantr)
   from S3 S8 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lenegcon2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>(\<cn>B) \<longleftrightarrow> B\<lsq>(\<cn>A)"
proof -
   have S1: "A \<in> \<real> \<and> (\<cn>B) \<in> \<real> \<longrightarrow> 
   A\<lsq>(\<cn>B) \<longleftrightarrow> (\<cn>(\<cn>B))\<lsq>(\<cn>A)" by (rule MMI_lenegt)
   have S2: "B \<in> \<real> \<longrightarrow> (\<cn>B) \<in> \<real>" by (rule MMI_renegclt)
   from S1 S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>(\<cn>B) \<longleftrightarrow> (\<cn>(\<cn>B))\<lsq>(\<cn>A)" by (rule MMI_sylan2)
   have S4: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S5: "B \<in> \<complex> \<longrightarrow> (\<cn>(\<cn>B)) = B" by (rule MMI_negnegt)
   from S4 S5 have S6: "B \<in> \<real> \<longrightarrow> (\<cn>(\<cn>B)) = B" by (rule MMI_syl)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> (\<cn>(\<cn>B)) = B" by (rule MMI_adantl)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>(\<cn>B))\<lsq>(\<cn>A) \<longleftrightarrow> B\<lsq>(\<cn>A)" by (rule MMI_breq1d)
   from S3 S8 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>(\<cn>B) \<longleftrightarrow> B\<lsq>(\<cn>A)" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lesub1t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> A \<cs> C\<lsq>B \<cs> C"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> (\<cn>C) \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> 
   A \<ca> (\<cn>C)\<lsq>B \<ca> (\<cn>C)" by (rule MMI_leadd1t)
   have S2: "C \<in> \<real> \<longrightarrow> (\<cn>C) \<in> \<real>" by (rule MMI_renegclt)
   from S1 S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> 
   A \<ca> (\<cn>C)\<lsq>B \<ca> (\<cn>C)" by (rule MMI_syl3an3)
   have S4: "A \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A \<ca> (\<cn>C) = A \<cs> C" by (rule MMI_negsubt)
   from S4 have S5: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A \<ca> (\<cn>C) = A \<cs> C" by (rule MMI_3adant2)
   have S6: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B \<ca> (\<cn>C) = B \<cs> C" by (rule MMI_negsubt)
   from S6 have S7: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B \<ca> (\<cn>C) = B \<cs> C" by (rule MMI_3adant1)
   from S5 S7 have S8: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> 
   A \<ca> (\<cn>C)\<lsq>B \<ca> (\<cn>C) \<longleftrightarrow> A \<cs> C\<lsq>B \<cs> C" by (rule MMI_breq12d)
   have S9: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S10: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S11: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S8 S9 S10 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<ca> (\<cn>C)\<lsq>B \<ca> (\<cn>C) \<longleftrightarrow> A \<cs> C\<lsq>B \<cs> C" by (rule MMI_syl3an)
   from S3 S12 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> A \<cs> C\<lsq>B \<cs> C" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lesub2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> C \<cs> B\<lsq>C \<cs> A"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)" by (rule MMI_lenegt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>(\<cn>A)" by (rule MMI_3adant3)
   have S3: "(\<cn>B) \<in> \<real> \<and> (\<cn>A) \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A)" by (rule MMI_leadd2t)
   have S4: "A \<in> \<real> \<longrightarrow> (\<cn>A) \<in> \<real>" by (rule MMI_renegclt)
   from S3 S4 have S5: "(\<cn>B) \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A)" by (rule MMI_syl3an2)
   have S6: "B \<in> \<real> \<longrightarrow> (\<cn>B) \<in> \<real>" by (rule MMI_renegclt)
   from S5 S6 have S7: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A)" by (rule MMI_syl3an1)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<lsq>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A)" by (rule MMI_3com12)
   have S9: "C \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>B) = C \<cs> B" by (rule MMI_negsubt)
   from S9 have S10: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>B) = C \<cs> B" by (rule MMI_3adant2)
   have S11: "C \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>A) = C \<cs> A" by (rule MMI_negsubt)
   from S11 have S12: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>A) = C \<cs> A" by (rule MMI_3adant3)
   from S10 S12 have S13: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A) \<longleftrightarrow> C \<cs> B\<lsq>C \<cs> A" by (rule MMI_breq12d)
   from S13 have S14: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A) \<longleftrightarrow> C \<cs> B\<lsq>C \<cs> A" by (rule MMI_3coml)
   have S15: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S16: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S17: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S14 S15 S16 S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C \<ca> (\<cn>B)\<lsq>C \<ca> (\<cn>A) \<longleftrightarrow> C \<cs> B\<lsq>C \<cs> A" by (rule MMI_syl3an)
   from S2 S8 S18 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<lsq>B \<longleftrightarrow> C \<cs> B\<lsq>C \<cs> A" by (rule MMI_3bitrd)
qed

lemma (in MMIsar0) MMI_ltsub2t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> C \<cs> B\<ls>C \<cs> A"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)" by (rule MMI_ltnegt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>(\<cn>A)" by (rule MMI_3adant3)
   have S3: "(\<cn>B) \<in> \<real> \<and> (\<cn>A) \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A)" by (rule MMI_ltadd2t)
   have S4: "A \<in> \<real> \<longrightarrow> (\<cn>A) \<in> \<real>" by (rule MMI_renegclt)
   from S3 S4 have S5: "(\<cn>B) \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A)" by (rule MMI_syl3an2)
   have S6: "B \<in> \<real> \<longrightarrow> (\<cn>B) \<in> \<real>" by (rule MMI_renegclt)
   from S5 S6 have S7: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A)" by (rule MMI_syl3an1)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   (\<cn>B)\<ls>(\<cn>A) \<longleftrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A)" by (rule MMI_3com12)
   have S9: "C \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>B) = C \<cs> B" by (rule MMI_negsubt)
   from S9 have S10: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>B) = C \<cs> B" by (rule MMI_3adant2)
   have S11: "C \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>A) = C \<cs> A" by (rule MMI_negsubt)
   from S11 have S12: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> C \<ca> (\<cn>A) = C \<cs> A" by (rule MMI_3adant3)
   from S10 S12 have S13: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A) \<longleftrightarrow> C \<cs> B\<ls>C \<cs> A" by (rule MMI_breq12d)
   from S13 have S14: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A) \<longleftrightarrow> C \<cs> B\<ls>C \<cs> A" by (rule MMI_3coml)
   have S15: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S16: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S17: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S14 S15 S16 S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   C \<ca> (\<cn>B)\<ls>C \<ca> (\<cn>A) \<longleftrightarrow> C \<cs> B\<ls>C \<cs> A" by (rule MMI_syl3an)
   from S2 S8 S18 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> C \<cs> B\<ls>C \<cs> A" by (rule MMI_3bitrd)
qed

lemma (in MMIsar0) MMI_ltaddpos: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_ltaddpost)
   from S1 S2 S3 show "\<zero>\<ls>A \<longleftrightarrow> B\<ls>B \<ca> A" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_posdif: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A" by (rule MMI_posdift)
   from S1 S2 S3 show "A\<ls>B \<longleftrightarrow> \<zero>\<ls>B \<cs> A" by (rule MMI_mp2an)
qed


(******************* 381 - 390 ****************************)

lemma (in MMIsar0) MMI_ltnegcon1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "(\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>A" by (rule MMI_ltnegcon1t)
   from S1 S2 S3 show "(\<cn>A)\<ls>B \<longleftrightarrow> (\<cn>B)\<ls>A" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_lenegcon1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "(\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>A" by (rule MMI_lenegcon1t)
   from S1 S2 S3 show "(\<cn>A)\<lsq>B \<longleftrightarrow> (\<cn>B)\<lsq>A" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_lt0neg1t: 
   shows "A \<in> \<real> \<longrightarrow> 
   A\<ls>\<zero> \<longleftrightarrow> \<zero>\<ls>(\<cn>A)"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "A \<in> \<real> \<and> \<zero> \<in> \<real> \<longrightarrow> 
   A\<ls>\<zero> \<longleftrightarrow> (\<cn>\<zero>)\<ls>(\<cn>A)" by (rule MMI_ltnegt)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> 
   A\<ls>\<zero> \<longleftrightarrow> (\<cn>\<zero>)\<ls>(\<cn>A)" by (rule MMI_mpan2)
   have S4: "(\<cn>\<zero>) = \<zero>" by (rule MMI_neg0)
   from S4 have S5: "(\<cn>\<zero>)\<ls>(\<cn>A) \<longleftrightarrow> \<zero>\<ls>(\<cn>A)" by (rule MMI_breq1i)
   from S3 S5 show "A \<in> \<real> \<longrightarrow> 
   A\<ls>\<zero> \<longleftrightarrow> \<zero>\<ls>(\<cn>A)" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_lt0neg2t: 
   shows "A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> (\<cn>A)\<ls>\<zero>"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> (\<cn>A)\<ls>(\<cn>\<zero>)" by (rule MMI_ltnegt)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> (\<cn>A)\<ls>(\<cn>\<zero>)" by (rule MMI_mpan)
   have S4: "(\<cn>\<zero>) = \<zero>" by (rule MMI_neg0)
   from S4 have S5: "(\<cn>A)\<ls>(\<cn>\<zero>) \<longleftrightarrow> (\<cn>A)\<ls>\<zero>" by (rule MMI_breq2i)
   from S3 S5 show "A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> (\<cn>A)\<ls>\<zero>" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_le0neg1t: 
   shows "A \<in> \<real> \<longrightarrow> 
   A\<lsq>\<zero> \<longleftrightarrow> \<zero>\<lsq>(\<cn>A)"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "A \<in> \<real> \<and> \<zero> \<in> \<real> \<longrightarrow> 
   A\<lsq>\<zero> \<longleftrightarrow> (\<cn>\<zero>)\<lsq>(\<cn>A)" by (rule MMI_lenegt)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> 
   A\<lsq>\<zero> \<longleftrightarrow> (\<cn>\<zero>)\<lsq>(\<cn>A)" by (rule MMI_mpan2)
   have S4: "(\<cn>\<zero>) = \<zero>" by (rule MMI_neg0)
   from S4 have S5: "(\<cn>\<zero>)\<lsq>(\<cn>A) \<longleftrightarrow> \<zero>\<lsq>(\<cn>A)" by (rule MMI_breq1i)
   from S3 S5 show "A \<in> \<real> \<longrightarrow> 
   A\<lsq>\<zero> \<longleftrightarrow> \<zero>\<lsq>(\<cn>A)" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_le0neg2t: 
   shows "A \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> (\<cn>A)\<lsq>\<zero>"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> (\<cn>A)\<lsq>(\<cn>\<zero>)" by (rule MMI_lenegt)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> (\<cn>A)\<lsq>(\<cn>\<zero>)" by (rule MMI_mpan)
   have S4: "(\<cn>\<zero>) = \<zero>" by (rule MMI_neg0)
   from S4 have S5: "(\<cn>A)\<lsq>(\<cn>\<zero>) \<longleftrightarrow> (\<cn>A)\<lsq>\<zero>" by (rule MMI_breq2i)
   from S3 S5 show "A \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> (\<cn>A)\<lsq>\<zero>" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_lesub0t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> A = \<zero>"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   B \<cs> A = B \<cs> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq2)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   B\<lsq>B \<cs> A \<longleftrightarrow> 
   B\<lsq>B \<cs> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> B\<lsq>B \<cs> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_anbi12d)
   have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) = \<zero>" by (rule MMI_eqeq1)
   from S4 S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> A = \<zero>) \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> B\<lsq>B \<cs> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) = \<zero>" by (rule MMI_bibi12d)
   have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B =  if(B \<in> \<real>, B, \<zero>)" by (rule MMI_id)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B \<cs> ( if(A \<in> \<real>, A, \<zero>)) = ( if(B \<in> \<real>, B, \<zero>)) \<cs> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq1)
   from S7 S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<lsq>B \<cs> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<cs> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq12d)
   from S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> B\<lsq>B \<cs> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<cs> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_anbi2d)
   from S10 have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> B\<lsq>B \<cs> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) = \<zero>) \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<cs> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) = \<zero>" by (rule MMI_bibi1d)
   have S12: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S12 have S13: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S14: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S14 have S15: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S13 S15 have S16: "\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> ( if(B \<in> \<real>, B, \<zero>))\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<cs> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) = \<zero>" by (rule MMI_lesub0)
   from S6 S11 S16 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<and> B\<lsq>B \<cs> A \<longleftrightarrow> A = \<zero>" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_mulge0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_opreq1)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A\<cdot>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_breq2d)
   from S2 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B) \<longleftrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>B)" by (rule MMI_imbi12d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longleftrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S7 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>B \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>B) \<longleftrightarrow> 
   (\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S12 S14 have S15: "\<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero>\<lsq>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero>\<lsq>( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_mulge0)
   from S5 S10 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_dedth2h)
   from S16 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero>\<lsq>A \<and> \<zero>\<lsq>B \<longrightarrow> \<zero>\<lsq>A\<cdot>B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltmsqt: 
   shows "A \<in> \<real> \<longrightarrow> 
   \<not>(A = \<zero>) \<longrightarrow> \<zero>\<ls>A\<cdot>A"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> 
    if(A \<in> \<real>, A, \<zero>) = \<zero>" by (rule MMI_eqeq1)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<not>(A = \<zero>) \<longleftrightarrow> 
   \<not>( if(A \<in> \<real>, A, \<zero>) = \<zero>)" by (rule MMI_negbid)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A =  if(A \<in> \<real>, A, \<zero>)" by (rule MMI_id)
   from S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A =  if(A \<in> \<real>, A, \<zero>)" .
   from S3 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq12d)
   from S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero>\<ls>A\<cdot>A \<longleftrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2d)
   from S2 S6 have S7: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<not>(A = \<zero>) \<longrightarrow> \<zero>\<ls>A\<cdot>A) \<longleftrightarrow> 
   (\<not>( if(A \<in> \<real>, A, \<zero>) = \<zero>) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S8: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S8 have S9: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S9 have S10: "\<not>( if(A \<in> \<real>, A, \<zero>) = \<zero>) \<longrightarrow> 
   \<zero>\<ls>( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_msqgt0)
   from S7 S10 show "A \<in> \<real> \<longrightarrow> 
   \<not>(A = \<zero>) \<longrightarrow> \<zero>\<ls>A\<cdot>A" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_lt01: 
   shows "\<zero>\<ls>\<one>"
proof -
   have S1: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   have S2: "\<one> \<noteq> \<zero> \<longleftrightarrow> \<not>(\<one> = \<zero>)" by (rule MMI_df_ne)
   from S1 S2 have S3: "\<not>(\<one> = \<zero>)" by (rule MMI_mpbi)
   have S4: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S4 have S5: "\<not>(\<one> = \<zero>) \<longrightarrow> 
   \<zero>\<ls>\<one>\<cdot>\<one>" by (rule MMI_msqgt0)
   from S3 S5 have S6: "\<zero>\<ls>\<one>\<cdot>\<one>" by (rule MMI_ax_mp)
   have S7: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 have S8: "\<one>\<cdot>\<one> = \<one>" by (rule MMI_mulid1)
   from S6 S8 show "\<zero>\<ls>\<one>" by (rule MMI_breqtr)
qed

(********* 391 - 400 ***********************)

lemma (in MMIsar0) MMI_eqneg: assumes A1: "A \<in> \<complex>"   
   shows "A = (\<cn>A) \<longleftrightarrow> A = \<zero>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S1 S2 have S3: "\<one> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   have S4: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S6: "\<zero>\<ls>\<one>" by (rule MMI_lt01)
   have S7: "\<zero>\<ls>\<one>" by (rule MMI_lt01)
   from S4 S5 S6 S7 have S8: "\<zero>\<ls>\<one> \<ca> \<one>" by (rule MMI_addgt0i)
   from S3 S8 have S9: "\<one> \<ca> \<one> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   have S10: "\<one> \<ca> \<one> \<noteq> \<zero> \<longleftrightarrow> 
   \<not>(\<one> \<ca> \<one> = \<zero>)" by (rule MMI_df_ne)
   from S9 S10 have S11: "\<not>(\<one> \<ca> \<one> = \<zero>)" by (rule MMI_mpbi)
   have S12: "A = (\<cn>A) \<longrightarrow> A \<ca> A = A \<ca> (\<cn>A)" by (rule MMI_opreq2)
   from A1 have S13: "A \<in> \<complex>".
   from S13 have S14: "(\<one> \<ca> \<one>)\<cdot>A = A \<ca> A" by (rule MMI_1p1times)
   from A1 have S15: "A \<in> \<complex>".
   from S15 have S16: "A \<ca> (\<cn>A) = \<zero>" by (rule MMI_negid)
   from S16 have S17: "\<zero> = A \<ca> (\<cn>A)" by (rule MMI_eqcomi)
   from S12 S14 S17 have S18: "A = (\<cn>A) \<longrightarrow> 
   (\<one> \<ca> \<one>)\<cdot>A = \<zero>" by (rule MMI_3eqtr4g)
   from S3 have S19: "\<one> \<ca> \<one> \<in> \<real>" .
   from S19 have S20: "\<one> \<ca> \<one> \<in> \<complex>" by (rule MMI_recn)
   from A1 have S21: "A \<in> \<complex>".
   from S20 S21 have S22: "(\<one> \<ca> \<one>)\<cdot>A = \<zero> \<longleftrightarrow> 
   \<one> \<ca> \<one> = \<zero> \<or> A = \<zero>" by (rule MMI_mul0or)
   from S18 S22 have S23: "A = (\<cn>A) \<longrightarrow> 
   \<one> \<ca> \<one> = \<zero> \<or> A = \<zero>" by (rule MMI_sylib)
   from S23 have S24: "A = (\<cn>A) \<longrightarrow> 
   \<not>(\<one> \<ca> \<one> = \<zero>) \<longrightarrow> A = \<zero>" by (rule MMI_ord)
   from S11 S24 have S25: "A = (\<cn>A) \<longrightarrow> A = \<zero>" by (rule MMI_mpi)
   have S26: "(\<cn>\<zero>) = \<zero> \<cs> \<zero>" by (rule MMI_df_neg)
   have S27: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S27 have S28: "\<zero> \<cs> \<zero> = \<zero>" by (rule MMI_subid)
   from S26 S28 have S29: "\<zero> = (\<cn>\<zero>)" by (rule MMI_eqtr2)
   have S30: "A = \<zero> \<longrightarrow> A = \<zero>" by (rule MMI_id)
   have S31: "A = \<zero> \<longrightarrow> (\<cn>A) = (\<cn>\<zero>)" by (rule MMI_negeq)
   from S30 S31 have S32: "A = \<zero> \<longrightarrow> 
   A = (\<cn>A) \<longleftrightarrow> \<zero> = (\<cn>\<zero>)" by (rule MMI_eqeq12d)
   from S29 S32 have S33: "A = \<zero> \<longrightarrow> A = (\<cn>A)" by (rule MMI_mpbiri)
   from S25 S33 show "A = (\<cn>A) \<longleftrightarrow> A = \<zero>" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_eqnegt: 
   shows "A \<in> \<complex> \<longrightarrow> 
   A = (\<cn>A) \<longleftrightarrow> A = \<zero>"
proof -
   have S1: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   A =  if(A \<in> \<complex>, A, \<zero>)" by (rule MMI_id)
   have S2: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   (\<cn>A) = (\<cn>( if(A \<in> \<complex>, A, \<zero>)))" by (rule MMI_negeq)
   from S1 S2 have S3: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   A = (\<cn>A) \<longleftrightarrow> 
    if(A \<in> \<complex>, A, \<zero>) = (\<cn>( if(A \<in> \<complex>, A, \<zero>)))" by (rule MMI_eqeq12d)
   have S4: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> 
    if(A \<in> \<complex>, A, \<zero>) = \<zero>" by (rule MMI_eqeq1)
   from S3 S4 have S5: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   (A = (\<cn>A) \<longleftrightarrow> A = \<zero>) \<longleftrightarrow> 
    if(A \<in> \<complex>, A, \<zero>) = (\<cn>( if(A \<in> \<complex>, A, \<zero>))) \<longleftrightarrow> 
    if(A \<in> \<complex>, A, \<zero>) = \<zero>" by (rule MMI_bibi12d)
   have S6: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S6 have S7: " if(A \<in> \<complex>, A, \<zero>) \<in> \<complex>" by (rule MMI_elimel)
   from S7 have S8: " if(A \<in> \<complex>, A, \<zero>) = (\<cn>( if(A \<in> \<complex>, A, \<zero>))) \<longleftrightarrow> 
    if(A \<in> \<complex>, A, \<zero>) = \<zero>" by (rule MMI_eqneg)
   from S5 S8 show "A \<in> \<complex> \<longrightarrow> 
   A = (\<cn>A) \<longleftrightarrow> A = \<zero>" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_negeq0t: 
   shows "A \<in> \<complex> \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> (\<cn>A) = \<zero>"
proof -
   have S1: "A \<in> \<complex> \<longrightarrow> (\<cn>(\<cn>A)) = A" by (rule MMI_negnegt)
   from S1 have S2: "A \<in> \<complex> \<longrightarrow> 
   (\<cn>A) = (\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>A) = A" by (rule MMI_eqeq2d)
   have S3: "(\<cn>A) = A \<longleftrightarrow> A = (\<cn>A)" by (rule MMI_eqcom)
   from S2 S3 have S4: "A \<in> \<complex> \<longrightarrow> 
   A = (\<cn>A) \<longleftrightarrow> (\<cn>A) = (\<cn>(\<cn>A))" by (rule MMI_syl6rbb)
   have S5: "A \<in> \<complex> \<longrightarrow> 
   A = (\<cn>A) \<longleftrightarrow> A = \<zero>" by (rule MMI_eqnegt)
   have S6: "A \<in> \<complex> \<longrightarrow> (\<cn>A) \<in> \<complex>" by (rule MMI_negclt)
   have S7: "(\<cn>A) \<in> \<complex> \<longrightarrow> 
   (\<cn>A) = (\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>A) = \<zero>" by (rule MMI_eqnegt)
   from S6 S7 have S8: "A \<in> \<complex> \<longrightarrow> 
   (\<cn>A) = (\<cn>(\<cn>A)) \<longleftrightarrow> (\<cn>A) = \<zero>" by (rule MMI_syl)
   from S4 S5 S8 show "A \<in> \<complex> \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> (\<cn>A) = \<zero>" by (rule MMI_3bitr3d)
qed

lemma (in MMIsar0) MMI_negne0: assumes A1: "A \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longleftrightarrow> (\<cn>A) \<noteq> \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> 
   A = \<zero> \<longleftrightarrow> (\<cn>A) = \<zero>" by (rule MMI_negeq0t)
   from S1 S2 have S3: "A = \<zero> \<longleftrightarrow> (\<cn>A) = \<zero>" by (rule MMI_ax_mp)
   from S3 show "A \<noteq> \<zero> \<longleftrightarrow> (\<cn>A) \<noteq> \<zero>" by (rule MMI_eqneqi)
qed

lemma (in MMIsar0) MMI_negn0: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "(\<cn>A) \<noteq> \<zero>"
proof -
   from A2 have S1: "A \<noteq> \<zero>".
   from A1 have S2: "A \<in> \<complex>".
   from S2 have S3: "A \<noteq> \<zero> \<longleftrightarrow> (\<cn>A) \<noteq> \<zero>" by (rule MMI_negne0)
   from S1 S3 show "(\<cn>A) \<noteq> \<zero>" by (rule MMI_mpbi)
qed

lemma (in MMIsar0) MMI_elimgt0: 
   shows "\<zero>\<ls>( if(\<zero>\<ls>A, A, \<one>))"
proof -
   have S1: "A =  if(\<zero>\<ls>A, A, \<one>) \<longrightarrow> 
   \<zero>\<ls>A \<longleftrightarrow> 
   \<zero>\<ls>( if(\<zero>\<ls>A, A, \<one>))" by (rule MMI_breq2)
   have S2: "\<one> =  if(\<zero>\<ls>A, A, \<one>) \<longrightarrow> 
   \<zero>\<ls>\<one> \<longleftrightarrow> 
   \<zero>\<ls>( if(\<zero>\<ls>A, A, \<one>))" by (rule MMI_breq2)
   have S3: "\<zero>\<ls>\<one>" by (rule MMI_lt01)
   from S1 S2 S3 show "\<zero>\<ls>( if(\<zero>\<ls>A, A, \<one>))" by (rule MMI_elimhyp)
qed

lemma (in MMIsar0) MMI_elimge0: 
   shows "\<zero>\<lsq>( if(\<zero>\<lsq>A, A, \<zero>))"
proof -
   have S1: "A =  if(\<zero>\<lsq>A, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>A \<longleftrightarrow> 
   \<zero>\<lsq>( if(\<zero>\<lsq>A, A, \<zero>))" by (rule MMI_breq2)
   have S2: "\<zero> =  if(\<zero>\<lsq>A, A, \<zero>) \<longrightarrow> 
   \<zero>\<lsq>\<zero> \<longleftrightarrow> 
   \<zero>\<lsq>( if(\<zero>\<lsq>A, A, \<zero>))" by (rule MMI_breq2)
   have S3: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S3 have S4: "\<zero>\<lsq>\<zero>" by (rule MMI_leid)
   from S1 S2 S4 show "\<zero>\<lsq>( if(\<zero>\<lsq>A, A, \<zero>))" by (rule MMI_elimhyp)
qed

lemma (in MMIsar0) MMI_ltp1t: 
   shows "A \<in> \<real> \<longrightarrow> A\<ls>A \<ca> \<one>"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S2: "A \<in> \<complex> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_ax0id)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_syl)
   have S4: "\<zero>\<ls>\<one>" by (rule MMI_lt01)
   have S5: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S6: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S7: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>\<one> \<longleftrightarrow> 
   A \<ca> \<zero>\<ls>A \<ca> \<one>" by (rule MMI_ltadd2t)
   from S5 S6 S7 have S8: "A \<in> \<real> \<longrightarrow> 
   \<zero>\<ls>\<one> \<longleftrightarrow> 
   A \<ca> \<zero>\<ls>A \<ca> \<one>" by (rule MMI_mp3an12)
   from S4 S8 have S9: "A \<in> \<real> \<longrightarrow> 
   A \<ca> \<zero>\<ls>A \<ca> \<one>" by (rule MMI_mpbii)
   from S3 S9 show "A \<in> \<real> \<longrightarrow> A\<ls>A \<ca> \<one>" by (rule MMI_eqbrtrrd)
qed

lemma (in MMIsar0) MMI_lep1t: 
   shows "A \<in> \<real> \<longrightarrow> A\<lsq>A \<ca> \<one>"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> A\<ls>A \<ca> \<one>" by (rule MMI_ltp1t)
   have S2: "A \<in> \<real> \<longrightarrow> A \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
   have S3: "A \<in> \<real> \<and> A \<ca> \<one> \<in> \<real> \<longrightarrow> 
   A\<ls>A \<ca> \<one> \<longrightarrow> A\<lsq>A \<ca> \<one>" by (rule MMI_ltlet)
   from S2 S3 have S4: "A \<in> \<real> \<longrightarrow> 
   A\<ls>A \<ca> \<one> \<longrightarrow> A\<lsq>A \<ca> \<one>" by (rule MMI_mpdan)
   from S1 S4 show "A \<in> \<real> \<longrightarrow> A\<lsq>A \<ca> \<one>" by (rule MMI_mpd)
qed

lemma (in MMIsar0) MMI_ltp1: assumes A1: "A \<in> \<real>"   
   shows "A\<ls>A \<ca> \<one>"
proof -
   from A1 have S1: "A \<in> \<real>".
   have S2: "A \<in> \<real> \<longrightarrow> A\<ls>A \<ca> \<one>" by (rule MMI_ltp1t)
   from S1 S2 show "A\<ls>A \<ca> \<one>" by (rule MMI_ax_mp)
qed

(************* 401 - 410 ************************)

lemma (in MMIsar0) MMI_recgt0i: assumes A1: "A \<in> \<real>" and
    A2: "\<zero> \<ls> A"   
   shows "\<zero> \<ls> \<one>\<cdiv>A"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S2: "A \<in> \<real>".
   from S2 have S3: "A \<in> \<complex>" by (rule MMI_recn)
   have S4: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "\<zero> \<ls> A".
   from S5 S6 have S7: "A \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S1 S3 S4 S7 have S8: "\<one>\<cdiv>A \<noteq> \<zero>" by (rule MMI_divne0)
   have S9: "\<one>\<cdiv>A \<noteq> \<zero> \<longleftrightarrow> 
   \<zero> \<noteq> \<one>\<cdiv>A" by (rule MMI_necom)
   from S8 S9 have S10: "\<zero> \<noteq> \<one>\<cdiv>A" by (rule MMI_mpbi)
   have S11: "\<zero> \<noteq> \<one>\<cdiv>A \<longleftrightarrow> 
   \<not>(\<zero> = \<one>\<cdiv>A)" by (rule MMI_df_ne)
   from S10 S11 have S12: "\<not>(\<zero> = \<one>\<cdiv>A)" by (rule MMI_mpbi)
   have S13: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S14: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S15: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S14 S15 have S16: "\<zero> \<ls> \<one> \<longrightarrow> \<not>(\<one> \<ls> \<zero>)" by (rule MMI_ltnsym)
   from S13 S16 have S17: "\<not>(\<one> \<ls> \<zero>)" by (rule MMI_ax_mp)
   from A2 have S18: "\<zero> \<ls> A".
   from A1 have S19: "A \<in> \<real>".
   from S7 have S20: "A \<noteq> \<zero>" .
   from S19 S20 have S21: "\<one>\<cdiv>A \<in> \<real>" by (rule MMI_rereccl)
   from S21 have S22: "(\<cn>(\<one>\<cdiv>A)) \<in> \<real>" by (rule MMI_renegcl)
   from A1 have S23: "A \<in> \<real>".
   from S22 S23 have S24: "\<zero> \<ls> (\<cn>(\<one>\<cdiv>A)) \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> (\<cn>(\<one>\<cdiv>A))\<cdot>A" by (rule MMI_mulgt0)
   from S18 S24 have S25: "\<zero> \<ls> (\<cn>(\<one>\<cdiv>A)) \<longrightarrow> 
   \<zero> \<ls> (\<cn>(\<one>\<cdiv>A))\<cdot>A" by (rule MMI_mpan2)
   from S21 have S26: "\<one>\<cdiv>A \<in> \<real>" .
   from S26 have S27: "\<one>\<cdiv>A \<in> \<complex>" by (rule MMI_recn)
   from S3 have S28: "A \<in> \<complex>" .
   from S27 S28 have S29: "(\<cn>(\<one>\<cdiv>A))\<cdot>A = (\<cn>((\<one>\<cdiv>A)\<cdot>A))" by (rule MMI_mulneg1)
   from S27 have S30: "\<one>\<cdiv>A \<in> \<complex>" .
   from S3 have S31: "A \<in> \<complex>" .
   from S30 S31 have S32: "(\<one>\<cdiv>A)\<cdot>A = A\<cdot>(\<one>\<cdiv>A)" by (rule MMI_mulcom)
   from S3 have S33: "A \<in> \<complex>" .
   from S7 have S34: "A \<noteq> \<zero>" .
   from S33 S34 have S35: "A\<cdot>(\<one>\<cdiv>A) = \<one>" by (rule MMI_recid)
   from S32 S35 have S36: "(\<one>\<cdiv>A)\<cdot>A = \<one>" by (rule MMI_eqtr)
   from S36 have S37: "(\<cn>((\<one>\<cdiv>A)\<cdot>A)) = (\<cn>\<one>)" by (rule MMI_negeqi)
   from S29 S37 have S38: "(\<cn>(\<one>\<cdiv>A))\<cdot>A = (\<cn>\<one>)" by (rule MMI_eqtr)
   from S25 S38 have S39: "\<zero> \<ls> (\<cn>(\<one>\<cdiv>A)) \<longrightarrow> \<zero> \<ls> (\<cn>\<one>)" by (rule MMI_syl6breq)
   from S21 have S40: "\<one>\<cdiv>A \<in> \<real>" .
   have S41: "\<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<one>\<cdiv>A \<ls> \<zero> \<longleftrightarrow> 
   \<zero> \<ls> (\<cn>(\<one>\<cdiv>A))" by (rule MMI_lt0neg1t)
   from S40 S41 have S42: "\<one>\<cdiv>A \<ls> \<zero> \<longleftrightarrow> 
   \<zero> \<ls> (\<cn>(\<one>\<cdiv>A))" by (rule MMI_ax_mp)
   have S43: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S44: "\<one> \<in> \<real> \<longrightarrow> 
   \<one> \<ls> \<zero> \<longleftrightarrow> \<zero> \<ls> (\<cn>\<one>)" by (rule MMI_lt0neg1t)
   from S43 S44 have S45: "\<one> \<ls> \<zero> \<longleftrightarrow> \<zero> \<ls> (\<cn>\<one>)" by (rule MMI_ax_mp)
   from S39 S42 S45 have S46: "\<one>\<cdiv>A \<ls> \<zero> \<longrightarrow> \<one> \<ls> \<zero>" by (rule MMI_3imtr4)
   from S17 S46 have S47: "\<not>(\<one>\<cdiv>A \<ls> \<zero>)" by (rule MMI_mto)
   from S12 S47 have S48: "\<not>(\<zero> = \<one>\<cdiv>A \<or> \<one>\<cdiv>A \<ls> \<zero>)" by (rule MMI_pm3_2ni)
   have S49: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S21 have S50: "\<one>\<cdiv>A \<in> \<real>" .
   have S51: "\<zero> \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<not>(\<zero> = \<one>\<cdiv>A \<or> \<one>\<cdiv>A \<ls> \<zero>)" by (rule MMI_axlttri)
   from S49 S50 S51 have S52: "\<zero> \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<not>(\<zero> = \<one>\<cdiv>A \<or> \<one>\<cdiv>A \<ls> \<zero>)" by (rule MMI_mp2an)
   from S48 S52 show "\<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_ltm1t: 
   shows "A \<in> \<real> \<longrightarrow> A \<cs> \<one> \<ls> A"
proof -
   have S1: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S2: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S4: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<longleftrightarrow> 
   A \<cs> \<one> \<ls> A \<cs> \<zero>" by (rule MMI_ltsub2t)
   from S2 S3 S4 have S5: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<longleftrightarrow> 
   A \<cs> \<one> \<ls> A \<cs> \<zero>" by (rule MMI_mp3an12)
   from S1 S5 have S6: "A \<in> \<real> \<longrightarrow> 
   A \<cs> \<one> \<ls> A \<cs> \<zero>" by (rule MMI_mpbii)
   have S7: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S8: "A \<in> \<complex> \<longrightarrow> A \<cs> \<zero> = A" by (rule MMI_subid1t)
   from S7 S8 have S9: "A \<in> \<real> \<longrightarrow> A \<cs> \<zero> = A" by (rule MMI_syl)
   from S6 S9 show "A \<in> \<real> \<longrightarrow> A \<cs> \<one> \<ls> A" by (rule MMI_breqtrd)
qed

lemma (in MMIsar0) MMI_letrp1t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<lsq> B \<longrightarrow> A \<lsq> B \<ca> \<one>"
proof -
   have S1: "B \<in> \<real> \<longrightarrow> B \<ls> B \<ca> \<one>" by (rule MMI_ltp1t)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<ls> B \<ca> \<one>" by (rule MMI_adantl)
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<and> B \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_lelttrt)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<and> B \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_3expb)
   have S5: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
   from S5 have S6: "B \<in> \<real> \<longrightarrow> 
   B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real>" by (rule MMI_ancli)
   from S4 S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<and> B \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_sylan2)
   from S2 S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_mpan2d)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<lsq> B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_3impia)
   have S10: "A \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<longrightarrow> 
   A \<ls> B \<ca> \<one> \<longrightarrow> A \<lsq> B \<ca> \<one>" by (rule MMI_ltlet)
   from S5 have S11: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   from S10 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<ca> \<one> \<longrightarrow> A \<lsq> B \<ca> \<one>" by (rule MMI_sylan2)
   from S12 have S13: "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<lsq> B \<longrightarrow> 
   A \<ls> B \<ca> \<one> \<longrightarrow> A \<lsq> B \<ca> \<one>" by (rule MMI_3adant3)
   from S9 S13 show "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<lsq> B \<longrightarrow> A \<lsq> B \<ca> \<one>" by (rule MMI_mpd)
qed

lemma (in MMIsar0) MMI_p1let: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<ca> \<one> \<lsq> B \<longrightarrow> A \<lsq> B"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> A \<lsq> A \<ca> \<one>" by (rule MMI_lep1t)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<lsq> A \<ca> \<one>" by (rule MMI_adantr)
   have S3: "A \<in> \<real> \<and> A \<ca> \<one> \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> A \<ca> \<one> \<and> A \<ca> \<one> \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_letrt)
   from S3 have S4: "(A \<in> \<real> \<and> A \<ca> \<one> \<in> \<real>) \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> A \<ca> \<one> \<and> A \<ca> \<one> \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_3expa)
   have S5: "A \<in> \<real> \<longrightarrow> A \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
   from S5 have S6: "A \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> A \<ca> \<one> \<in> \<real>" by (rule MMI_ancli)
   from S4 S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> A \<ca> \<one> \<and> A \<ca> \<one> \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_sylan)
   from S2 S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> \<one> \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_mpand)
   from S8 show "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<ca> \<one> \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_3impia)
qed

lemma (in MMIsar0) MMI_prodgt0lem: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero> \<ls> A"   
   shows "\<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A3 have S2: "\<zero> \<ls> A".
   from S1 S2 have S3: "\<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_recgt0i)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from S5 S6 have S7: "A\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   from A1 have S8: "A \<in> \<real>".
   from A1 have S9: "A \<in> \<real>".
   from A3 have S10: "\<zero> \<ls> A".
   from S9 S10 have S11: "A \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S8 S11 have S12: "\<one>\<cdiv>A \<in> \<real>" by (rule MMI_rereccl)
   from S4 S7 S12 have S13: "\<zero> \<ls> \<one>\<cdiv>A \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longrightarrow> 
   \<zero>\<cdot>(\<one>\<cdiv>A) \<ls> A\<cdot>B\<cdot>(\<one>\<cdiv>A)" by (rule MMI_ltmullem)
   from S3 S13 have S14: "\<zero> \<ls> A\<cdot>B \<longrightarrow> 
   \<zero>\<cdot>(\<one>\<cdiv>A) \<ls> A\<cdot>B\<cdot>(\<one>\<cdiv>A)" by (rule MMI_ax_mp)
   from S12 have S15: "\<one>\<cdiv>A \<in> \<real>" .
   from S15 have S16: "\<one>\<cdiv>A \<in> \<complex>" by (rule MMI_recn)
   from S16 have S17: "\<zero>\<cdot>(\<one>\<cdiv>A) = \<zero>" by (rule MMI_mul02)
   from A1 have S18: "A \<in> \<real>".
   from S18 have S19: "A \<in> \<complex>" by (rule MMI_recn)
   from A2 have S20: "B \<in> \<real>".
   from S20 have S21: "B \<in> \<complex>" by (rule MMI_recn)
   from S16 have S22: "\<one>\<cdiv>A \<in> \<complex>" .
   from S19 S21 S22 have S23: "A\<cdot>B\<cdot>(\<one>\<cdiv>A) = A\<cdot>(\<one>\<cdiv>A)\<cdot>B" by (rule MMI_mul23)
   from S19 have S24: "A \<in> \<complex>" .
   from S11 have S25: "A \<noteq> \<zero>" .
   from S24 S25 have S26: "A\<cdot>(\<one>\<cdiv>A) = \<one>" by (rule MMI_recid)
   from S26 have S27: "A\<cdot>(\<one>\<cdiv>A)\<cdot>B = \<one>\<cdot>B" by (rule MMI_opreq1i)
   from S21 have S28: "B \<in> \<complex>" .
   from S28 have S29: "\<one>\<cdot>B = B" by (rule MMI_mulid2)
   from S23 S27 S29 have S30: "A\<cdot>B\<cdot>(\<one>\<cdiv>A) = B" by (rule MMI_3eqtr)
   from S14 S17 S30 show "\<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_3brtr3g)
qed

lemma (in MMIsar0) MMI_prodgt0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "\<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<ls> A \<or> \<zero> = A" by (rule MMI_leloe)
   have S4: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   A\<cdot>B = ( if(\<zero> \<ls> A, A, \<one>))\<cdot>B" by (rule MMI_opreq1)
   from S4 have S5: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longleftrightarrow> 
   \<zero> \<ls> ( if(\<zero> \<ls> A, A, \<one>))\<cdot>B" by (rule MMI_breq2d)
   from S5 have S6: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   (\<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(\<zero> \<ls> A, A, \<one>))\<cdot>B \<longrightarrow> \<zero> \<ls> B)" by (rule MMI_imbi1d)
   from A1 have S7: "A \<in> \<real>".
   have S8: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S7 S8 have S9: " if(\<zero> \<ls> A, A, \<one>) \<in> \<real>" by (rule MMI_keepel)
   from A2 have S10: "B \<in> \<real>".
   have S11: "\<zero> \<ls> ( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_elimgt0)
   from S9 S10 S11 have S12: "\<zero> \<ls> ( if(\<zero> \<ls> A, A, \<one>))\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_prodgt0lem)
   from S6 S12 have S13: "\<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_dedth)
   have S14: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S14 have S15: "\<not>(\<zero> \<ls> \<zero>)" by (rule MMI_ltnr)
   have S16: "\<zero> = A \<longrightarrow> \<zero>\<cdot>B = A\<cdot>B" by (rule MMI_opreq1)
   from A2 have S17: "B \<in> \<real>".
   from S17 have S18: "B \<in> \<complex>" by (rule MMI_recn)
   from S18 have S19: "\<zero>\<cdot>B = \<zero>" by (rule MMI_mul02)
   from S16 S19 have S20: "\<zero> = A \<longrightarrow> \<zero> = A\<cdot>B" by (rule MMI_syl5eqr)
   from S20 have S21: "\<zero> = A \<longrightarrow> 
   \<zero> \<ls> \<zero> \<longleftrightarrow> \<zero> \<ls> A\<cdot>B" by (rule MMI_breq2d)
   from S15 S21 have S22: "\<zero> = A \<longrightarrow> 
   \<not>(\<zero> \<ls> A\<cdot>B)" by (rule MMI_mtbii)
   from S22 have S23: "\<zero> = A \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_pm2_21d)
   from S13 S23 have S24: "\<zero> \<ls> A \<or> \<zero> = A \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_jaoi)
   from S3 S24 have S25: "\<zero> \<lsq> A \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_sylbi)
   from S25 show "\<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_prodge0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S2 have S3: "(\<cn>B) \<in> \<real>" by (rule MMI_renegcl)
   from S1 S3 have S4: "\<zero> \<ls> A \<and> \<zero> \<ls> (\<cn>B) \<longrightarrow> \<zero> \<ls> A\<cdot>(\<cn>B)" by (rule MMI_mulgt0)
   from S4 have S5: "\<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> (\<cn>B) \<longrightarrow> \<zero> \<ls> A\<cdot>(\<cn>B)" by (rule MMI_ex)
   from A2 have S6: "B \<in> \<real>".
   have S7: "B \<in> \<real> \<longrightarrow> 
   B \<ls> \<zero> \<longleftrightarrow> \<zero> \<ls> (\<cn>B)" by (rule MMI_lt0neg1t)
   from S6 S7 have S8: "B \<ls> \<zero> \<longleftrightarrow> \<zero> \<ls> (\<cn>B)" by (rule MMI_ax_mp)
   from A1 have S9: "A \<in> \<real>".
   from A2 have S10: "B \<in> \<real>".
   from S9 S10 have S11: "A\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   have S12: "A\<cdot>B \<in> \<real> \<longrightarrow> 
   A\<cdot>B \<ls> \<zero> \<longleftrightarrow> 
   \<zero> \<ls> (\<cn>(A\<cdot>B))" by (rule MMI_lt0neg1t)
   from S11 S12 have S13: "A\<cdot>B \<ls> \<zero> \<longleftrightarrow> 
   \<zero> \<ls> (\<cn>(A\<cdot>B))" by (rule MMI_ax_mp)
   from A1 have S14: "A \<in> \<real>".
   from S14 have S15: "A \<in> \<complex>" by (rule MMI_recn)
   from A2 have S16: "B \<in> \<real>".
   from S16 have S17: "B \<in> \<complex>" by (rule MMI_recn)
   from S15 S17 have S18: "A\<cdot>(\<cn>B) = (\<cn>(A\<cdot>B))" by (rule MMI_mulneg2)
   from S18 have S19: "\<zero> \<ls> A\<cdot>(\<cn>B) \<longleftrightarrow> 
   \<zero> \<ls> (\<cn>(A\<cdot>B))" by (rule MMI_breq2i)
   from S13 S19 have S20: "A\<cdot>B \<ls> \<zero> \<longleftrightarrow> \<zero> \<ls> A\<cdot>(\<cn>B)" by (rule MMI_bitr4)
   from S5 S8 S20 have S21: "\<zero> \<ls> A \<longrightarrow> 
   B \<ls> \<zero> \<longrightarrow> A\<cdot>B \<ls> \<zero>" by (rule MMI_3imtr4g)
   from S21 have S22: "\<zero> \<ls> A \<longrightarrow> 
   \<not>(A\<cdot>B \<ls> \<zero>) \<longrightarrow> \<not>(B \<ls> \<zero>)" by (rule MMI_con3d)
   have S23: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S24: "A\<cdot>B \<in> \<real>" .
   from S23 S24 have S25: "\<zero> \<lsq> A\<cdot>B \<longleftrightarrow> 
   \<not>(A\<cdot>B \<ls> \<zero>)" by (rule MMI_lenlt)
   have S26: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S27: "B \<in> \<real>".
   from S26 S27 have S28: "\<zero> \<lsq> B \<longleftrightarrow> \<not>(B \<ls> \<zero>)" by (rule MMI_lenlt)
   from S22 S25 S28 have S29: "\<zero> \<ls> A \<longrightarrow> 
   \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B" by (rule MMI_3imtr4g)
   from S29 show "\<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltmul1i: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>" and
    A4: "\<zero> \<ls> C"   
   shows "A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C"
proof -
   from A4 have S1: "\<zero> \<ls> C".
   from A1 have S2: "A \<in> \<real>".
   from A2 have S3: "B \<in> \<real>".
   from A3 have S4: "C \<in> \<real>".
   from S2 S3 S4 have S5: "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_ltmullem)
   from S1 S5 have S6: "A \<ls> B \<longrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_ax_mp)
   from A3 have S7: "C \<in> \<real>".
   from A4 have S8: "\<zero> \<ls> C".
   from S7 S8 have S9: "\<zero> \<ls> \<one>\<cdiv>C" by (rule MMI_recgt0i)
   from A1 have S10: "A \<in> \<real>".
   from A3 have S11: "C \<in> \<real>".
   from S10 S11 have S12: "A\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S13: "B \<in> \<real>".
   from A3 have S14: "C \<in> \<real>".
   from S13 S14 have S15: "B\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from A3 have S16: "C \<in> \<real>".
   from A3 have S17: "C \<in> \<real>".
   from A4 have S18: "\<zero> \<ls> C".
   from S17 S18 have S19: "C \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S16 S19 have S20: "\<one>\<cdiv>C \<in> \<real>" by (rule MMI_rereccl)
   from S12 S15 S20 have S21: "\<zero> \<ls> \<one>\<cdiv>C \<longrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<longrightarrow> 
   A\<cdot>C\<cdot>(\<one>\<cdiv>C) \<ls> B\<cdot>C\<cdot>(\<one>\<cdiv>C)" by (rule MMI_ltmullem)
   from S9 S21 have S22: "A\<cdot>C \<ls> B\<cdot>C \<longrightarrow> 
   A\<cdot>C\<cdot>(\<one>\<cdiv>C) \<ls> B\<cdot>C\<cdot>(\<one>\<cdiv>C)" by (rule MMI_ax_mp)
   from A1 have S23: "A \<in> \<real>".
   from S23 have S24: "A \<in> \<complex>" by (rule MMI_recn)
   from A3 have S25: "C \<in> \<real>".
   from S25 have S26: "C \<in> \<complex>" by (rule MMI_recn)
   from S26 have S27: "C \<in> \<complex>" .
   from S19 have S28: "C \<noteq> \<zero>" .
   from S27 S28 have S29: "\<one>\<cdiv>C \<in> \<complex>" by (rule MMI_reccl)
   from S24 S26 S29 have S30: "A\<cdot>C\<cdot>(\<one>\<cdiv>C) = A\<cdot>(C\<cdot>(\<one>\<cdiv>C))" by (rule MMI_mulass)
   from S26 have S31: "C \<in> \<complex>" .
   from S19 have S32: "C \<noteq> \<zero>" .
   from S31 S32 have S33: "C\<cdot>(\<one>\<cdiv>C) = \<one>" by (rule MMI_recid)
   from S33 have S34: "A\<cdot>(C\<cdot>(\<one>\<cdiv>C)) = A\<cdot>\<one>" by (rule MMI_opreq2i)
   from S24 have S35: "A \<in> \<complex>" .
   from S35 have S36: "A\<cdot>\<one> = A" by (rule MMI_mulid1)
   from S30 S34 S36 have S37: "A\<cdot>C\<cdot>(\<one>\<cdiv>C) = A" by (rule MMI_3eqtr)
   from A2 have S38: "B \<in> \<real>".
   from S38 have S39: "B \<in> \<complex>" by (rule MMI_recn)
   from S26 have S40: "C \<in> \<complex>" .
   from S29 have S41: "\<one>\<cdiv>C \<in> \<complex>" .
   from S39 S40 S41 have S42: "B\<cdot>C\<cdot>(\<one>\<cdiv>C) = B\<cdot>(C\<cdot>(\<one>\<cdiv>C))" by (rule MMI_mulass)
   from S33 have S43: "C\<cdot>(\<one>\<cdiv>C) = \<one>" .
   from S43 have S44: "B\<cdot>(C\<cdot>(\<one>\<cdiv>C)) = B\<cdot>\<one>" by (rule MMI_opreq2i)
   from S39 have S45: "B \<in> \<complex>" .
   from S45 have S46: "B\<cdot>\<one> = B" by (rule MMI_mulid1)
   from S42 S44 S46 have S47: "B\<cdot>C\<cdot>(\<one>\<cdiv>C) = B" by (rule MMI_3eqtr)
   from S22 S37 S47 have S48: "A\<cdot>C \<ls> B\<cdot>C \<longrightarrow> A \<ls> B" by (rule MMI_3brtr3g)
   from S6 S48 show "A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_ltmul1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C"
proof -
   have S1: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   A\<cdot>C = A\<cdot>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_opreq2)
   have S2: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   B\<cdot>C = B\<cdot>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_opreq2)
   from S1 S2 have S3: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<longleftrightarrow> 
   A\<cdot>( if(\<zero> \<ls> C, C, \<one>)) \<ls> B\<cdot>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_breq12d)
   from S3 have S4: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C) \<longleftrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   A\<cdot>( if(\<zero> \<ls> C, C, \<one>)) \<ls> B\<cdot>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_bibi2d)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from A3 have S7: "C \<in> \<real>".
   have S8: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S7 S8 have S9: " if(\<zero> \<ls> C, C, \<one>) \<in> \<real>" by (rule MMI_keepel)
   have S10: "\<zero> \<ls> ( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_elimgt0)
   from S5 S6 S9 S10 have S11: "A \<ls> B \<longleftrightarrow> 
   A\<cdot>( if(\<zero> \<ls> C, C, \<one>)) \<ls> B\<cdot>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_ltmul1i)
   from S4 S11 show "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_ltdiv1i: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>" and
    A4: "\<zero> \<ls> C"   
   shows "A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from A3 have S4: "C \<in> \<real>".
   from A4 have S5: "\<zero> \<ls> C".
   from S4 S5 have S6: "C \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S3 S6 have S7: "\<one>\<cdiv>C \<in> \<real>" by (rule MMI_rereccl)
   from A3 have S8: "C \<in> \<real>".
   from A4 have S9: "\<zero> \<ls> C".
   from S8 S9 have S10: "\<zero> \<ls> \<one>\<cdiv>C" by (rule MMI_recgt0i)
   from S1 S2 S7 S10 have S11: "A \<ls> B \<longleftrightarrow> 
   A\<cdot>(\<one>\<cdiv>C) \<ls> B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_ltmul1i)
   from A1 have S12: "A \<in> \<real>".
   from S12 have S13: "A \<in> \<complex>" by (rule MMI_recn)
   from A3 have S14: "C \<in> \<real>".
   from S14 have S15: "C \<in> \<complex>" by (rule MMI_recn)
   from S6 have S16: "C \<noteq> \<zero>" .
   from S13 S15 S16 have S17: "A\<cdiv>C = A\<cdot>(\<one>\<cdiv>C)" by (rule MMI_divrec)
   from A2 have S18: "B \<in> \<real>".
   from S18 have S19: "B \<in> \<complex>" by (rule MMI_recn)
   from S15 have S20: "C \<in> \<complex>" .
   from S6 have S21: "C \<noteq> \<zero>" .
   from S19 S20 S21 have S22: "B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_divrec)
   from S17 S22 have S23: "A\<cdiv>C \<ls> B\<cdiv>C \<longleftrightarrow> 
   A\<cdot>(\<one>\<cdiv>C) \<ls> B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_breq12i)
   from S11 S23 show "A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_bitr4)
qed

(*********** 411 - 420 ********************************)

lemma (in MMIsar0) MMI_ltdiv1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C"
proof -
   have S1: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   A\<cdiv>C = A\<cdiv>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_opreq2)
   have S2: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   B\<cdiv>C = B\<cdiv>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_opreq2)
   from S1 S2 have S3: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   A\<cdiv>C \<ls> B\<cdiv>C \<longleftrightarrow> 
   A\<cdiv>( if(\<zero> \<ls> C, C, \<one>)) \<ls> B\<cdiv>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_breq12d)
   from S3 have S4: "C =  if(\<zero> \<ls> C, C, \<one>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C) \<longleftrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   A\<cdiv>( if(\<zero> \<ls> C, C, \<one>)) \<ls> B\<cdiv>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_bibi2d)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from A3 have S7: "C \<in> \<real>".
   have S8: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S7 S8 have S9: " if(\<zero> \<ls> C, C, \<one>) \<in> \<real>" by (rule MMI_keepel)
   have S10: "\<zero> \<ls> ( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_elimgt0)
   from S5 S6 S9 S10 have S11: "A \<ls> B \<longleftrightarrow> 
   A\<cdiv>( if(\<zero> \<ls> C, C, \<one>)) \<ls> B\<cdiv>( if(\<zero> \<ls> C, C, \<one>))" by (rule MMI_ltdiv1i)
   from S4 S11 show "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_ltmuldiv: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C \<ls> B \<longleftrightarrow> A \<ls> B\<cdiv>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A3 have S2: "C \<in> \<real>".
   from S1 S2 have S3: "A\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S4: "B \<in> \<real>".
   from A3 have S5: "C \<in> \<real>".
   from S3 S4 S5 have S6: "\<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C \<ls> B \<longleftrightarrow> 
   A\<cdot>C\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_ltdiv1)
   from A3 have S7: "C \<in> \<real>".
   from S7 have S8: "\<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from A3 have S9: "C \<in> \<real>".
   from S9 have S10: "C \<in> \<complex>" by (rule MMI_recn)
   from A1 have S11: "A \<in> \<real>".
   from S11 have S12: "A \<in> \<complex>" by (rule MMI_recn)
   from S10 S12 have S13: "C \<noteq> \<zero> \<longrightarrow> A\<cdot>C\<cdiv>C = A" by (rule MMI_divcan4z)
   from S8 S13 have S14: "\<zero> \<ls> C \<longrightarrow> A\<cdot>C\<cdiv>C = A" by (rule MMI_syl)
   from S14 have S15: "\<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C\<cdiv>C \<ls> B\<cdiv>C \<longleftrightarrow> A \<ls> B\<cdiv>C" by (rule MMI_breq1d)
   from S6 S15 show "\<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C \<ls> B \<longleftrightarrow> A \<ls> B\<cdiv>C" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_prodgt0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_opreq1)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_breq2d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_anbi12d)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B) \<longleftrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longrightarrow> \<zero> \<ls> B)" by (rule MMI_imbi1d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S8 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longrightarrow> \<zero> \<ls> B) \<longleftrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S12 S14 have S15: "\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_prodgt0)
   from S5 S10 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_dedth2h)
   from S16 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_prodgt02t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> B \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> A"
proof -
   have S1: "(B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> B \<and> \<zero> \<ls> B\<cdot>A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_prodgt0t)
   from S1 have S2: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<and> \<zero> \<ls> B\<cdot>A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_ex)
   from S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<and> \<zero> \<ls> B\<cdot>A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_ancoms)
   have S4: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_axmulcom)
   have S5: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S6: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S4 S5 S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_syl2an)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longleftrightarrow> \<zero> \<ls> B\<cdot>A" by (rule MMI_breq2d)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> B\<cdot>A" by (rule MMI_biimpd)
   from S3 S9 have S10: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> A" by (rule MMI_sylan2d)
   from S10 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> B \<and> \<zero> \<ls> A\<cdot>B \<longrightarrow> \<zero> \<ls> A" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_prodge0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_opreq1)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A\<cdot>B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_breq2d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_anbi12d)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longrightarrow> \<zero> \<lsq> B)" by (rule MMI_imbi1d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S6 have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S8 S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<longrightarrow> \<zero> \<lsq> B) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S13 have S14: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S12 S14 have S15: "\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_prodge0)
   from S5 S10 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B" by (rule MMI_dedth2h)
   from S16 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_prodge02t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> A"
proof -
   have S1: "(B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<lsq> B\<cdot>A \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_prodge0t)
   from S1 have S2: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<and> \<zero> \<lsq> B\<cdot>A \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_ex)
   from S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<and> \<zero> \<lsq> B\<cdot>A \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_ancoms)
   have S4: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_axmulcom)
   have S5: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S6: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S4 S5 S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_syl2an)
   from S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A\<cdot>B \<longleftrightarrow> \<zero> \<lsq> B\<cdot>A" by (rule MMI_breq2d)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> B\<cdot>A" by (rule MMI_biimpd)
   from S3 S9 have S10: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_sylan2d)
   from S10 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<lsq> A\<cdot>B \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltmul1t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>C = ( if(A \<in> \<real>, A, \<zero>))\<cdot>C" by (rule MMI_opreq1)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> B\<cdot>C" by (rule MMI_breq1d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> B\<cdot>C" by (rule MMI_bibi12d)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C) \<longleftrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> B\<cdot>C)" by (rule MMI_imbi2d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<cdot>C = ( if(B \<in> \<real>, B, \<zero>))\<cdot>C" by (rule MMI_opreq1)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> B\<cdot>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>C" by (rule MMI_breq2d)
   from S6 S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> B\<cdot>C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>C" by (rule MMI_bibi12d)
   from S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> B\<cdot>C) \<longleftrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>C)" by (rule MMI_imbi2d)
   have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   \<zero> \<ls> C \<longleftrightarrow> 
   \<zero> \<ls> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<cdot>C = ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   from S12 S13 have S14: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq12d)
   from S14 have S15: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_bibi2d)
   from S11 S15 have S16: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>C) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>)))" by (rule MMI_imbi12d)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S19: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S19 have S20: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S21: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S21 have S22: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S18 S20 S22 have S23: "\<zero> \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_ltmul1)
   from S5 S10 S16 S23 have S24: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_dedth3h)
   from S24 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltmul2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_ltmul1t)
   have S2: "A \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_axmulcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 have S4: "A \<in> \<real> \<and> C \<in> \<complex> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_sylan)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<complex> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_3adant2)
   have S6: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_axmulcom)
   have S7: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S6 S7 have S8: "B \<in> \<real> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_sylan)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_3adant1)
   from S5 S9 have S10: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<complex> \<longrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_breq12d)
   have S11: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S10 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_syl3an3)
   from S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_adantr)
   from S1 S13 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lemul1t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>C \<ls> B\<cdot>C" by (rule MMI_ltmul1t)
   have S2: "(A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex>) \<and> C \<noteq> \<zero> \<longrightarrow> 
   A\<cdot>C = B\<cdot>C \<longleftrightarrow> A = B" by (rule MMI_mulcan2t)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S5: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S3 S4 S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex>" by (rule MMI_3anim123i)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex>" by (rule MMI_adantr)
   have S8: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S8 have S9: "(A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_adantll)
   from S9 have S10: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_3adantl2)
   from S2 S7 S10 have S11: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C = B\<cdot>C \<longleftrightarrow> A = B" by (rule MMI_sylanc)
   from S11 have S12: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A = B \<longleftrightarrow> A\<cdot>C = B\<cdot>C" by (rule MMI_bicomd)
   from S1 S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<or> A = B \<longleftrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<or> A\<cdot>C = B\<cdot>C" by (rule MMI_orbi12d)
   have S14: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_leloet)
   from S14 have S15: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_3adant3)
   from S15 have S16: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_adantr)
   have S17: "A\<cdot>C \<in> \<real> \<and> B\<cdot>C \<in> \<real> \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<longleftrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<or> A\<cdot>C = B\<cdot>C" by (rule MMI_leloet)
   have S18: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S18 have S19: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_3adant2)
   have S20: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S20 have S21: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_3adant1)
   from S17 S19 S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<longleftrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<or> A\<cdot>C = B\<cdot>C" by (rule MMI_sylanc)
   from S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<longleftrightarrow> 
   A\<cdot>C \<ls> B\<cdot>C \<or> A\<cdot>C = B\<cdot>C" by (rule MMI_adantr)
   from S13 S16 S23 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_3bitr4d)
qed

lemma (in MMIsar0) MMI_lemul2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_lemul1t)
   have S2: "A \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_axmulcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_3adant2)
   have S7: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_axmulcom)
   have S8: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S4 have S9: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" .
   from S7 S8 S9 have S10: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_syl2an)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_3adant1)
   from S6 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_breq12d)
   from S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_adantr)
   from S1 S13 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_bitrd)
qed

(******** 421 - 430 *****************************)

lemma (in MMIsar0) MMI_ltmul2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_ltmul2t)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_ex)
   from S1 S2 S3 S5 show "\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdot>A \<ls> C\<cdot>B" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_lemul1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_lemul1t)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_ex)
   from S1 S2 S3 S5 show "\<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_lemul2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   have S4: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_lemul2t)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_ex)
   from S1 S2 S3 S5 show "\<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_lemul1it: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> C \<longleftrightarrow> 
   \<zero> \<ls> C \<or> \<zero> = C" by (rule MMI_leloet)
   from S1 S2 have S3: "C \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> C \<longleftrightarrow> 
   \<zero> \<ls> C \<or> \<zero> = C" by (rule MMI_mpan)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> C \<longleftrightarrow> 
   \<zero> \<ls> C \<or> \<zero> = C" by (rule MMI_3ad2ant3)
   have S5: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_lemul1t)
   from S5 have S6: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_biimpd)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_ex)
   have S8: "\<zero> = C \<longrightarrow> A\<cdot>\<zero> = A\<cdot>C" by (rule MMI_opreq2)
   have S9: "\<zero> = C \<longrightarrow> B\<cdot>\<zero> = B\<cdot>C" by (rule MMI_opreq2)
   from S8 S9 have S10: "\<zero> = C \<longrightarrow> 
   A\<cdot>\<zero> \<lsq> B\<cdot>\<zero> \<longleftrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_breq12d)
   have S11: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S11 have S12: "\<zero> \<lsq> \<zero>" by (rule MMI_leid)
   have S13: "A \<in> \<complex> \<longrightarrow> A\<cdot>\<zero> = \<zero>" by (rule MMI_mul01t)
   have S14: "B \<in> \<complex> \<longrightarrow> B\<cdot>\<zero> = \<zero>" by (rule MMI_mul01t)
   from S13 S14 have S15: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> 
   A\<cdot>\<zero> \<lsq> B\<cdot>\<zero> \<longleftrightarrow> \<zero> \<lsq> \<zero>" by (rule MMI_breqan12d)
   have S16: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S17: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S15 S16 S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<cdot>\<zero> \<lsq> B\<cdot>\<zero> \<longleftrightarrow> \<zero> \<lsq> \<zero>" by (rule MMI_syl2an)
   from S12 S18 have S19: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<cdot>\<zero> \<lsq> B\<cdot>\<zero>" by (rule MMI_mpbiri)
   from S10 S19 have S20: "\<zero> = C \<longrightarrow> 
   A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_syl5bi)
   from S20 have S21: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> = C \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_com12)
   from S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> = C \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_3adant3)
   from S22 have S23: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> = C \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_a1dd)
   from S7 S23 have S24: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<or> \<zero> = C \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_jaod)
   from S4 S24 have S25: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> C \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_sylbid)
   from S25 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_imp32)
qed

lemma (in MMIsar0) MMI_lemul2it: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> C\<cdot>A \<lsq> C\<cdot>B"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_lemul1it)
   have S2: "A \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_axmulcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_3adant2)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> A\<cdot>C = C\<cdot>A" by (rule MMI_adantr)
   have S8: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_axmulcom)
   have S9: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S4 have S10: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" .
   from S8 S9 S10 have S11: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_syl2an)
   from S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_3adant1)
   from S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_adantr)
   from S1 S7 S13 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> C\<cdot>A \<lsq> C\<cdot>B" by (rule MMI_3brtr3d)
qed

lemma (in MMIsar0) MMI_ltmul12it: 
   shows "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> A\<cdot>C \<ls> B\<cdot>D"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<lsq> C \<and> A \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_lemul1it)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_adantr)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   from S4 have S5: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_adantr)
   have S6: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_pm3_26)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_adantl)
   from S3 S5 S7 have S8: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3jca)
   from S8 have S9: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> 
   A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_adantr)
   have S10: "\<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> \<zero> \<lsq> C" by (rule MMI_pm3_26)
   from S10 have S11: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> \<zero> \<lsq> C" by (rule MMI_ad2antll)
   have S12: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longrightarrow> A \<lsq> B" by (rule MMI_ltlet)
   from S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> A \<ls> B \<longrightarrow> A \<lsq> B" by (rule MMI_imp)
   from S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> A \<lsq> B" by (rule MMI_adantrl)
   from S14 have S15: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> A \<lsq> B" by (rule MMI_ad2ant2r)
   from S11 S15 have S16: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> 
   \<zero> \<lsq> C \<and> A \<lsq> B" by (rule MMI_jca)
   from S1 S9 S16 have S17: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>C" by (rule MMI_sylanc)
   have S18: "(C \<in> \<real> \<and> D \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   C \<ls> D \<longleftrightarrow> B\<cdot>C \<ls> B\<cdot>D" by (rule MMI_ltmul2t)
   from S7 have S19: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> C \<in> \<real>" .
   have S20: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> D \<in> \<real>" by (rule MMI_pm3_27)
   from S20 have S21: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> D \<in> \<real>" by (rule MMI_adantl)
   from S5 have S22: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B \<in> \<real>" .
   from S19 S21 S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   C \<in> \<real> \<and> D \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_3jca)
   from S23 have S24: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> 
   C \<in> \<real> \<and> D \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_adantr)
   have S25: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S26: "\<zero> \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_lelttrt)
   from S25 S26 have S27: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_mp3an1)
   from S27 have S28: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_imp)
   from S28 have S29: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_adantlr)
   from S18 S24 S29 have S30: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B \<longrightarrow> 
   C \<ls> D \<longleftrightarrow> B\<cdot>C \<ls> B\<cdot>D" by (rule MMI_sylanc)
   from S30 have S31: "(((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B) \<and> C \<ls> D \<longrightarrow> B\<cdot>C \<ls> B\<cdot>D" by (rule MMI_biimpa)
   from S31 have S32: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> C \<ls> D \<longrightarrow> B\<cdot>C \<ls> B\<cdot>D" by (rule MMI_anasss)
   from S32 have S33: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> B\<cdot>C \<ls> B\<cdot>D" by (rule MMI_adantrrl)
   have S34: "A\<cdot>C \<in> \<real> \<and> B\<cdot>C \<in> \<real> \<and> B\<cdot>D \<in> \<real> \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<and> B\<cdot>C \<ls> B\<cdot>D \<longrightarrow> A\<cdot>C \<ls> B\<cdot>D" by (rule MMI_lelttrt)
   have S35: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S35 have S36: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_ad2ant2r)
   have S37: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S37 have S38: "B \<in> \<real> \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_adantrr)
   from S38 have S39: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_adantll)
   have S40: "B \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B\<cdot>D \<in> \<real>" by (rule MMI_axmulrcl)
   from S40 have S41: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B\<cdot>D \<in> \<real>" by (rule MMI_ad2ant2l)
   from S34 S36 S39 S41 have S42: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<and> B\<cdot>C \<ls> B\<cdot>D \<longrightarrow> A\<cdot>C \<ls> B\<cdot>D" by (rule MMI_syl3anc)
   from S42 have S43: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> 
   A\<cdot>C \<lsq> B\<cdot>C \<and> B\<cdot>C \<ls> B\<cdot>D \<longrightarrow> A\<cdot>C \<ls> B\<cdot>D" by (rule MMI_adantr)
   from S17 S33 S43 have S44: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<ls> B) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> A\<cdot>C \<ls> B\<cdot>D" by (rule MMI_mp2and)
   from S44 show "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<ls> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> C \<and> C \<ls> D \<longrightarrow> A\<cdot>C \<ls> B\<cdot>D" by (rule MMI_an4s)
qed

lemma (in MMIsar0) MMI_lemul12it: 
   shows "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>D"
proof -
   have S1: "A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S1 have S2: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_ad2ant2r)
   from S2 have S3: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<in> \<real>" by (rule MMI_adantr)
   have S4: "A \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> A\<cdot>D \<in> \<real>" by (rule MMI_axmulrcl)
   from S4 have S5: "(A \<in> \<real> \<and> D \<in> \<real>) \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>D \<in> \<real>" by (rule MMI_adantr)
   from S5 have S6: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> A\<cdot>D \<in> \<real>" by (rule MMI_an42s)
   from S6 have S7: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>D \<in> \<real>" by (rule MMI_adantr)
   have S8: "B \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B\<cdot>D \<in> \<real>" by (rule MMI_axmulrcl)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> B\<cdot>D \<in> \<real>" by (rule MMI_ad2ant2l)
   from S9 have S10: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> B\<cdot>D \<in> \<real>" by (rule MMI_adantr)
   have S11: "(C \<in> \<real> \<and> D \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> A \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_lemul2it)
   from S11 have S12: "C \<in> \<real> \<and> D \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_ex)
   from S12 have S13: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_3expa)
   from S13 have S14: "A \<in> \<real> \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_ancoms)
   have S15: "\<zero> \<lsq> A \<and> A \<lsq> B \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_pm3_26)
   have S16: "\<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> C \<lsq> D" by (rule MMI_pm3_27)
   from S14 S15 S16 have S17: "A \<in> \<real> \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_syl2ani)
   from S17 have S18: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_adantlr)
   from S18 have S19: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> A\<cdot>D" by (rule MMI_imp)
   have S20: "\<zero> \<lsq> A \<and> A \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_pm3_27)
   from S20 have S21: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> A \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_a1i)
   have S22: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S23: "\<zero> \<in> \<real> \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<lsq> D" by (rule MMI_letrt)
   from S22 S23 have S24: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<lsq> D" by (rule MMI_mp3an1)
   from S21 S24 have S25: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> 
   A \<lsq> B \<and> \<zero> \<lsq> D" by (rule MMI_im2anan9)
   have S26: "(A \<in> \<real> \<and> B \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> D \<and> A \<lsq> B \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_lemul1it)
   from S26 have S27: "A \<in> \<real> \<and> B \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> D \<and> A \<lsq> B \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_ex)
   from S27 have S28: "A \<in> \<real> \<and> B \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<and> \<zero> \<lsq> D \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_ancomsd)
   from S28 have S29: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> D \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<and> \<zero> \<lsq> D \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_3expa)
   from S29 have S30: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<and> \<zero> \<lsq> D \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_adantrl)
   from S25 S30 have S31: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_syld)
   from S31 have S32: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>D \<lsq> B\<cdot>D" by (rule MMI_imp)
   from S3 S7 S10 S19 S32 have S33: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> C \<in> \<real> \<and> D \<in> \<real>) \<and> (\<zero> \<lsq> A \<and> A \<lsq> B) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>D" by (rule MMI_letrd)
   from S33 show "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<lsq> C \<and> C \<lsq> D \<longrightarrow> A\<cdot>C \<lsq> B\<cdot>D" by (rule MMI_an4s)
qed

lemma (in MMIsar0) MMI_mulgt1t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> \<one> \<ls> A\<cdot>B"
proof -
   have S1: "\<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> \<one> \<ls> A" by (rule MMI_pm3_26)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> \<one> \<ls> A" by (rule MMI_a1i)
   have S3: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S6: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_axlttrn)
   from S4 S5 S6 have S7: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mp3an12)
   from S3 S7 have S8: "A \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mpani)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_adantr)
   have S10: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S11: "(\<one> \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_ltmul2t)
   from S11 have S12: "(\<one> \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_biimpd)
   from S12 have S13: "\<one> \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_ex)
   from S10 S13 have S14: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_mp3an1)
   from S14 have S15: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_ancoms)
   from S9 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_syld)
   from S16 have S17: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_imp3a)
   have S18: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S19: "A \<in> \<complex> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_ax1id)
   from S18 S19 have S20: "A \<in> \<real> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_syl)
   from S20 have S21: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_adantr)
   from S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A\<cdot>\<one> \<ls> A\<cdot>B \<longleftrightarrow> A \<ls> A\<cdot>B" by (rule MMI_breq1d)
   from S17 S22 have S23: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> A \<ls> A\<cdot>B" by (rule MMI_sylibd)
   from S2 S23 have S24: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> 
   \<one> \<ls> A \<and> A \<ls> A\<cdot>B" by (rule MMI_jcad)
   have S25: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>B \<in> \<real>" by (rule MMI_axmulrcl)
   have S26: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S27: "\<one> \<in> \<real> \<and> A \<in> \<real> \<and> A\<cdot>B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> A \<ls> A\<cdot>B \<longrightarrow> \<one> \<ls> A\<cdot>B" by (rule MMI_axlttrn)
   from S26 S27 have S28: "A \<in> \<real> \<and> A\<cdot>B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> A \<ls> A\<cdot>B \<longrightarrow> \<one> \<ls> A\<cdot>B" by (rule MMI_mp3an1)
   from S25 S28 have S29: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> A \<ls> A\<cdot>B \<longrightarrow> \<one> \<ls> A\<cdot>B" by (rule MMI_syldan)
   from S24 S29 have S30: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> \<one> \<ls> A\<cdot>B" by (rule MMI_syld)
   from S30 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<one> \<ls> A \<and> \<one> \<ls> B \<longrightarrow> \<one> \<ls> A\<cdot>B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltmulgt11t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A \<ls> A\<cdot>B"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "(\<one> \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_ltmul2t)
   from S1 S2 have S3: "(B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_mp3anl1)
   from S3 have S4: "B \<in> \<real> \<and> A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_3impa)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A\<cdot>\<one> \<ls> A\<cdot>B" by (rule MMI_3com12)
   have S6: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S7: "A \<in> \<complex> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_ax1id)
   from S6 S7 have S8: "A \<in> \<real> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_syl)
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_3ad2ant1)
   from S9 have S10: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>\<one> \<ls> A\<cdot>B \<longleftrightarrow> A \<ls> A\<cdot>B" by (rule MMI_breq1d)
   from S5 S10 show "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A \<ls> A\<cdot>B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_ltmulgt12t: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A \<ls> B\<cdot>A"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A \<ls> A\<cdot>B" by (rule MMI_ltmulgt11t)
   have S2: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_axmulcom)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S4: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A\<cdot>B = B\<cdot>A" by (rule MMI_3adant3)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<ls> A\<cdot>B \<longleftrightarrow> A \<ls> B\<cdot>A" by (rule MMI_breq2d)
   from S1 S7 show "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> B \<longleftrightarrow> A \<ls> B\<cdot>A" by (rule MMI_bitrd)
qed

 (*********** 431 - 440 **************************)

lemma (in MMIsar0) MMI_lemulge11t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> A \<lsq> A\<cdot>B"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S2: "A \<in> \<complex> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_ax1id)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_syl)
   from S3 have S4: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_ad2antrr)
   have S5: "((A \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> A) \<and> (\<one> \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> \<one> \<and> \<one> \<lsq> B \<longrightarrow> 
   A\<cdot>\<one> \<lsq> A\<cdot>B" by (rule MMI_lemul12it)
   have S6: "A \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> A \<in> \<real>" by (rule MMI_pm3_2)
   from S6 have S7: "A \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> A \<in> \<real>" by (rule MMI_pm2_43i)
   from S7 have S8: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   A \<in> \<real> \<and> A \<in> \<real>" by (rule MMI_ad2antrr)
   have S9: "\<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_pm3_26)
   from S9 have S10: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_adantl)
   have S11: "A \<in> \<real> \<longrightarrow> A \<lsq> A" by (rule MMI_leidt)
   from S11 have S12: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> A \<lsq> A" by (rule MMI_ad2antrr)
   from S10 S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   \<zero> \<lsq> A \<and> A \<lsq> A" by (rule MMI_jca)
   from S8 S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   (A \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> A" by (rule MMI_jca)
   have S15: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   from S15 have S16: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> B \<in> \<real>" by (rule MMI_adantr)
   have S17: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S16 S17 have S18: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   \<one> \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_jctil)
   have S19: "\<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> \<one> \<lsq> B" by (rule MMI_pm3_27)
   from S19 have S20: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> \<one> \<lsq> B" by (rule MMI_adantl)
   have S21: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S22: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S23: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S21 S22 S23 have S24: "\<zero> \<lsq> \<one>" by (rule MMI_ltlei)
   from S20 S24 have S25: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   \<zero> \<lsq> \<one> \<and> \<one> \<lsq> B" by (rule MMI_jctil)
   from S18 S25 have S26: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   (\<one> \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> \<one> \<and> \<one> \<lsq> B" by (rule MMI_jca)
   from S5 S14 S26 have S27: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> 
   A\<cdot>\<one> \<lsq> A\<cdot>B" by (rule MMI_sylanc)
   from S4 S27 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<one> \<lsq> B \<longrightarrow> A \<lsq> A\<cdot>B" by auto(*by (rule MMI_eqbrtrrd)*)
qed

lemma (in MMIsar0) MMI_ltdiv1t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdiv>C = ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C" by (rule MMI_opreq1)
   from S2 have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdiv>C \<ls> B\<cdiv>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_breq1d)
   from S1 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_bibi12d)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C) \<longleftrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> B\<cdiv>C)" by (rule MMI_imbi2d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<cdiv>C = ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C" by (rule MMI_opreq1)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> B\<cdiv>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C" by (rule MMI_breq2d)
   from S6 S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> B\<cdiv>C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C" by (rule MMI_bibi12d)
   from S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> B\<cdiv>C) \<longleftrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C)" by (rule MMI_imbi2d)
   have S11: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   \<zero> \<ls> C \<longleftrightarrow> 
   \<zero> \<ls> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   have S12: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C = ( if(A \<in> \<real>, A, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C = ( if(B \<in> \<real>, B, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_opreq2)
   from S12 S13 have S14: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq12d)
   from S14 have S15: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_bibi2d)
   from S11 S15 have S16: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> C \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>C \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>C) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>)))" by (rule MMI_imbi12d)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S19: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S19 have S20: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S21: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S21 have S22: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S18 S20 S22 have S23: "\<zero> \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdiv>( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_ltdiv1)
   from S5 S10 S16 S23 have S24: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_dedth3h)
   from S24 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdiv>C \<ls> B\<cdiv>C" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_lediv1t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdiv>C \<lsq> B\<cdiv>C"
proof -
   have S1: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdiv>C \<ls> A\<cdiv>C" by (rule MMI_ltdiv1t)
   from S1 have S2: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdiv>C \<ls> A\<cdiv>C" by (rule MMI_ex)
   from S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdiv>C \<ls> A\<cdiv>C" by (rule MMI_3com12)
   from S3 have S4: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdiv>C \<ls> A\<cdiv>C" by (rule MMI_imp)
   from S4 have S5: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   \<not>(B \<ls> A) \<longleftrightarrow> 
   \<not>(B\<cdiv>C \<ls> A\<cdiv>C)" by (rule MMI_negbid)
   have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> \<not>(B \<ls> A)" by (rule MMI_lenltt)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> \<not>(B \<ls> A)" by (rule MMI_3adant3)
   from S7 have S8: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> \<not>(B \<ls> A)" by (rule MMI_adantr)
   have S9: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S9 have S10: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_adantll)
   from S10 have S11: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_3adantl1)
   have S12: "A \<in> \<real> \<and> C \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> A\<cdiv>C \<in> \<real>" by (rule MMI_redivclt)
   from S12 have S13: "(A \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> A\<cdiv>C \<in> \<real>" by (rule MMI_3expa)
   from S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> A\<cdiv>C \<in> \<real>" by (rule MMI_3adantl2)
   have S15: "B \<in> \<real> \<and> C \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> B\<cdiv>C \<in> \<real>" by (rule MMI_redivclt)
   from S15 have S16: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> B\<cdiv>C \<in> \<real>" by (rule MMI_3expa)
   from S16 have S17: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> B\<cdiv>C \<in> \<real>" by (rule MMI_3adantl1)
   from S14 S17 have S18: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> 
   A\<cdiv>C \<in> \<real> \<and> B\<cdiv>C \<in> \<real>" by (rule MMI_jca)
   from S11 S18 have S19: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>C \<in> \<real> \<and> B\<cdiv>C \<in> \<real>" by (rule MMI_syldan)
   have S20: "A\<cdiv>C \<in> \<real> \<and> B\<cdiv>C \<in> \<real> \<longrightarrow> 
   A\<cdiv>C \<lsq> B\<cdiv>C \<longleftrightarrow> 
   \<not>(B\<cdiv>C \<ls> A\<cdiv>C)" by (rule MMI_lenltt)
   from S19 S20 have S21: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>C \<lsq> B\<cdiv>C \<longleftrightarrow> 
   \<not>(B\<cdiv>C \<ls> A\<cdiv>C)" by (rule MMI_syl)
   from S5 S8 S21 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdiv>C \<lsq> B\<cdiv>C" by (rule MMI_3bitr4d)
qed

lemma (in MMIsar0) MMI_gt0divt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> \<zero> \<ls> A\<cdiv>B"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "(\<zero> \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero>\<cdiv>B \<ls> A\<cdiv>B" by (rule MMI_ltdiv1t)
   from S1 S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero>\<cdiv>B \<ls> A\<cdiv>B" by (rule MMI_mp3anl1)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero>\<cdiv>B \<ls> A\<cdiv>B" by (rule MMI_3impa)
   have S5: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S6: "B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> \<zero>\<cdiv>B = \<zero>" by (rule MMI_div0t)
   have S7: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S6 S7 have S8: "B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> \<zero>\<cdiv>B = \<zero>" by (rule MMI_sylan)
   from S5 S8 have S9: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> \<zero>\<cdiv>B = \<zero>" by (rule MMI_syldan)
   from S9 have S10: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero>\<cdiv>B \<ls> A\<cdiv>B \<longleftrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_breq1d)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero>\<cdiv>B \<ls> A\<cdiv>B \<longleftrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_3adant1)
   from S4 S11 show "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_ge0divt: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>B"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "(\<zero> \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero>\<cdiv>B \<lsq> A\<cdiv>B" by (rule MMI_lediv1t)
   from S1 S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero>\<cdiv>B \<lsq> A\<cdiv>B" by (rule MMI_mp3anl1)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero>\<cdiv>B \<lsq> A\<cdiv>B" by (rule MMI_3impa)
   have S5: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S6: "B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> \<zero>\<cdiv>B = \<zero>" by (rule MMI_div0t)
   have S7: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S6 S7 have S8: "B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> \<zero>\<cdiv>B = \<zero>" by (rule MMI_sylan)
   from S5 S8 have S9: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> \<zero>\<cdiv>B = \<zero>" by (rule MMI_syldan)
   from S9 have S10: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero>\<cdiv>B \<lsq> A\<cdiv>B \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_breq1d)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero>\<cdiv>B \<lsq> A\<cdiv>B \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_3adant1)
   from S4 S11 show "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_divgt0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_gt0divt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_biimpd)
   from S2 have S3: "A \<in> \<real> \<longrightarrow> 
   B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_3exp)
   from S3 have S4: "A \<in> \<real> \<longrightarrow> 
   B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_com34)
   from S4 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_imp43)
qed

lemma (in MMIsar0) MMI_divge0t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<lsq> A\<cdiv>B"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_ge0divt)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_biimpd)
   from S2 have S3: "A \<in> \<real> \<longrightarrow> 
   B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<lsq> A \<longrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_3exp)
   from S3 have S4: "A \<in> \<real> \<longrightarrow> 
   B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_com34)
   from S4 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_imp43)
qed

lemma (in MMIsar0) MMI_divgt0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_divgt0t)
   from S1 S2 S3 show "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_mpanl12)
qed

lemma (in MMIsar0) MMI_divge0: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<lsq> A\<cdiv>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_divge0t)
   from S1 S2 S3 show "\<zero> \<lsq> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<lsq> A\<cdiv>B" by (rule MMI_mpanl12)
qed

lemma (in MMIsar0) MMI_divgt0i2: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero> \<ls> B"   
   shows "\<zero> \<ls> A \<longrightarrow> \<zero> \<ls> A\<cdiv>B"
proof -
   from A3 have S1: "\<zero> \<ls> B".
   from A1 have S2: "A \<in> \<real>".
   from A2 have S3: "B \<in> \<real>".
   from S2 S3 have S4: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_divgt0)
   from S1 S4 show "\<zero> \<ls> A \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_mpan2)
qed

 (************************ 441 - 450 ***************************)


lemma (in MMIsar0) MMI_divgt0i: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero> \<ls> A" and
    A4: "\<zero> \<ls> B"   
   shows "\<zero> \<ls> A\<cdiv>B"
proof -
   from A3 have S1: "\<zero> \<ls> A".
   from A1 have S2: "A \<in> \<real>".
   from A2 have S3: "B \<in> \<real>".
   from A4 have S4: "\<zero> \<ls> B".
   from S2 S3 S4 have S5: "\<zero> \<ls> A \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_divgt0i2)
   from S1 S5 show "\<zero> \<ls> A\<cdiv>B" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_recgt0t: 
   shows "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S3: "(\<one> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> \<one> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_divgt0t)
   from S2 S3 have S4: "(\<one> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_mpanr1)
   from S1 S4 show "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_mpanl1)
qed

lemma (in MMIsar0) MMI_recgt0: assumes A1: "A \<in> \<real>"   
   shows "\<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   have S2: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_recgt0t)
   from S1 S2 show "\<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_ltmuldivt: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdiv>B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>B" by (rule MMI_opreq1)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<ls> C" by (rule MMI_breq1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ls> C\<cdiv>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>B" by (rule MMI_breq1)
   from S2 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A\<cdot>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdiv>B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>B" by (rule MMI_bibi12d)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdiv>B) \<longleftrightarrow> 
   (\<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>B)" by (rule MMI_imbi2d)
   have S6: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S7: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S7 have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> C" by (rule MMI_breq1d)
   have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   C\<cdiv>B = C\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S8 S10 have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   from S6 S11 have S12: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>B \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>B) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S13: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>))" by (rule MMI_breq2)
   have S14: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   C\<cdiv>( if(B \<in> \<real>, B, \<zero>)) = ( if(C \<in> \<real>, C, \<zero>))\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq1)
   from S14 have S15: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>))\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S13 S15 have S16: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>( if(B \<in> \<real>, B, \<zero>))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>))\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   from S16 have S17: "C =  if(C \<in> \<real>, C, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> C \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> C\<cdiv>( if(B \<in> \<real>, B, \<zero>))) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>))\<cdiv>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi2d)
   have S18: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S18 have S19: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S20: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S20 have S21: " if(C \<in> \<real>, C, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S22: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S22 have S23: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S19 S21 S23 have S24: "\<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(C \<in> \<real>, C, \<zero>))\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_ltmuldiv)
   from S5 S12 S17 S24 have S25: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdiv>B" by (rule MMI_dedth3h)
   from S25 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdiv>B" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltmuldiv2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> B \<ls> C\<cdiv>A"
proof -
   have S1: "B \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_axmulcom)
   have S2: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 S3 have S4: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_syl2an)
   from S4 have S5: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_3adant3)
   from S5 have S6: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_adantr)
   from S6 have S7: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   B\<cdot>A \<ls> C \<longleftrightarrow> A\<cdot>B \<ls> C" by (rule MMI_breq1d)
   have S8: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   B\<cdot>A \<ls> C \<longleftrightarrow> B \<ls> C\<cdiv>A" by (rule MMI_ltmuldivt)
   from S7 S8 have S9: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> B \<ls> C\<cdiv>A" by (rule MMI_bitr3d)
   from S9 have S10: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> B \<ls> C\<cdiv>A" by (rule MMI_ex)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> B \<ls> C\<cdiv>A" by (rule MMI_3com12)
   from S11 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<ls> C \<longleftrightarrow> B \<ls> C\<cdiv>A" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltdivmult: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A \<ls> B\<cdot>C"
proof -
   have S1: "(A \<in> \<real> \<and> B\<cdot>C \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B\<cdot>C \<longleftrightarrow> 
   A\<cdiv>B \<ls> B\<cdot>C\<cdiv>B" by (rule MMI_ltdiv1t)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   have S3: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_3adant1)
   have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S2 S4 S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> B\<cdot>C \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_3jca)
   from S1 S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B\<cdot>C \<longleftrightarrow> 
   A\<cdiv>B \<ls> B\<cdot>C\<cdiv>B" by (rule MMI_sylan)
   have S8: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S8 have S9: "B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_ex)
   from S9 have S10: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_adantr)
   have S11: "B \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_divcan3t)
   from S11 have S12: "B \<in> \<complex> \<longrightarrow> 
   C \<in> \<complex> \<longrightarrow> 
   B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_3exp)
   from S12 have S13: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> 
   B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_imp)
   have S14: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S15: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S13 S14 S15 have S16: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_syl2an)
   from S10 S16 have S17: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_syld)
   from S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_3adant1)
   from S18 have S19: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_imp)
   from S19 have S20: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> B\<cdot>C\<cdiv>B \<longleftrightarrow> A\<cdiv>B \<ls> C" by (rule MMI_breq2d)
   from S7 S20 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A \<ls> B\<cdot>C" by (rule MMI_bitr2d)
qed

lemma (in MMIsar0) MMI_ledivmult: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A \<lsq> B\<cdot>C"
proof -
   have S1: "(A \<in> \<real> \<and> B\<cdot>C \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B\<cdot>C \<longleftrightarrow> 
   A\<cdiv>B \<lsq> B\<cdot>C\<cdiv>B" by (rule MMI_lediv1t)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   have S3: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_axmulrcl)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C \<in> \<real>" by (rule MMI_3adant1)
   have S5: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S2 S4 S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> B\<cdot>C \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_3jca)
   from S1 S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B\<cdot>C \<longleftrightarrow> 
   A\<cdiv>B \<lsq> B\<cdot>C\<cdiv>B" by (rule MMI_sylan)
   have S8: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S8 have S9: "B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_ex)
   from S9 have S10: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_adantr)
   have S11: "B \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_divcan3t)
   from S11 have S12: "B \<in> \<complex> \<longrightarrow> 
   C \<in> \<complex> \<longrightarrow> 
   B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_3exp)
   from S12 have S13: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> 
   B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_imp)
   have S14: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S15: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S13 S14 S15 have S16: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<noteq> \<zero> \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_syl2an)
   from S10 S16 have S17: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_syld)
   from S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> B \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_3adant1)
   from S18 have S19: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B\<cdot>C\<cdiv>B = C" by (rule MMI_imp)
   from S19 have S20: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> B\<cdot>C\<cdiv>B \<longleftrightarrow> A\<cdiv>B \<lsq> C" by (rule MMI_breq2d)
   from S7 S20 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A \<lsq> B\<cdot>C" by (rule MMI_bitr2d)
qed

lemma (in MMIsar0) MMI_ltdivmul2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdot>B"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A \<ls> B\<cdot>C" by (rule MMI_ltdivmult)
   have S2: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_axmulcom)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_3adant1)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_adantr)
   from S7 have S8: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B\<cdot>C \<longleftrightarrow> A \<ls> C\<cdot>B" by (rule MMI_breq2d)
   from S1 S8 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A \<ls> C\<cdot>B" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lt2mul2divt: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdot>B \<ls> C\<cdot>D \<longleftrightarrow> A\<cdiv>D \<ls> C\<cdiv>B"
proof -
   have S1: "C \<in> \<complex> \<and> D \<in> \<complex> \<longrightarrow> C\<cdot>D = D\<cdot>C" by (rule MMI_axmulcom)
   have S2: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   have S3: "D \<in> \<real> \<longrightarrow> D \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 S3 have S4: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> C\<cdot>D = D\<cdot>C" by (rule MMI_syl2an)
   from S4 have S5: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   C\<cdot>D\<cdiv>B = D\<cdot>C\<cdiv>B" by (rule MMI_opreq1d)
   from S5 have S6: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdot>D\<cdiv>B = D\<cdot>C\<cdiv>B" by (rule MMI_3ad2ant2)
   have S7: "(D \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex>) \<and> B \<noteq> \<zero> \<longrightarrow> 
   D\<cdot>C\<cdiv>B = D\<cdot>(C\<cdiv>B)" by (rule MMI_divasst)
   from S3 have S8: "D \<in> \<real> \<longrightarrow> D \<in> \<complex>" .
   from S8 have S9: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> D \<in> \<complex>" by (rule MMI_ad2antlr)
   from S9 have S10: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> D \<in> \<complex>" by (rule MMI_3adant1)
   from S2 have S11: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" .
   from S11 have S12: "B \<in> \<real> \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_ad2antrl)
   from S12 have S13: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> C \<in> \<complex>" by (rule MMI_3adant3)
   have S14: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S14 have S15: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<complex>" by (rule MMI_3ad2ant1)
   from S10 S13 S15 have S16: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   D \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_3jca)
   have S17: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S17 have S18: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_3adant2)
   from S7 S16 S18 have S19: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   D\<cdot>C\<cdiv>B = D\<cdot>(C\<cdiv>B)" by (rule MMI_sylanc)
   from S6 S19 have S20: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdot>D\<cdiv>B = D\<cdot>(C\<cdiv>B)" by (rule MMI_eqtrd)
   from S20 have S21: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   C\<cdot>D\<cdiv>B = D\<cdot>(C\<cdiv>B)" by (rule MMI_3adant3r)
   from S21 have S22: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   C\<cdot>D\<cdiv>B = D\<cdot>(C\<cdiv>B)" by (rule MMI_3adant1l)
   from S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A \<ls> C\<cdot>D\<cdiv>B \<longleftrightarrow> A \<ls> D\<cdot>(C\<cdiv>B)" by (rule MMI_breq2d)
   have S24: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C\<cdot>D \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<ls> C\<cdot>D \<longleftrightarrow> A \<ls> C\<cdot>D\<cdiv>B" by (rule MMI_ltmuldivt)
   have S25: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S25 have S26: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> A \<in> \<real>" by (rule MMI_3ad2ant1)
   have S27: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   from S27 have S28: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> B \<in> \<real>" by (rule MMI_3ad2ant1)
   have S29: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> C\<cdot>D \<in> \<real>" by (rule MMI_axmulrcl)
   from S29 have S30: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> C\<cdot>D \<in> \<real>" by (rule MMI_3ad2ant2)
   from S26 S28 S30 have S31: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A \<in> \<real> \<and> B \<in> \<real> \<and> C\<cdot>D \<in> \<real>" by (rule MMI_3jca)
   have S32: "\<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> B" by (rule MMI_pm3_26)
   from S32 have S33: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> B" by (rule MMI_3ad2ant3)
   from S24 S31 S33 have S34: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdot>B \<ls> C\<cdot>D \<longleftrightarrow> A \<ls> C\<cdot>D\<cdiv>B" by (rule MMI_sylanc)
   have S35: "(A \<in> \<real> \<and> D \<in> \<real> \<and> C\<cdiv>B \<in> \<real>) \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdiv>D \<ls> C\<cdiv>B \<longleftrightarrow> A \<ls> D\<cdot>(C\<cdiv>B)" by (rule MMI_ltdivmult)
   from S26 have S36: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> A \<in> \<real>" .
   have S37: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> D \<in> \<real>" by (rule MMI_pm3_27)
   from S37 have S38: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> D \<in> \<real>" by (rule MMI_3ad2ant2)
   have S39: "C \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_redivclt)
   have S40: "C \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> C \<in> \<real>" by (rule MMI_3simp1)
   have S41: "C \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S17 have S42: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   from S42 have S43: "C \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_3adant1)
   from S39 S40 S41 S43 have S44: "C \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_syl3anc)
   from S44 have S45: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3com12)
   from S45 have S46: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3adant3r)
   from S46 have S47: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3adant2r)
   from S47 have S48: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3adant1l)
   from S36 S38 S48 have S49: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A \<in> \<real> \<and> D \<in> \<real> \<and> C\<cdiv>B \<in> \<real>" by (rule MMI_3jca)
   have S50: "\<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> D" by (rule MMI_pm3_27)
   from S50 have S51: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> D" by (rule MMI_3ad2ant3)
   from S35 S49 S51 have S52: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdiv>D \<ls> C\<cdiv>B \<longleftrightarrow> A \<ls> D\<cdot>(C\<cdiv>B)" by (rule MMI_sylanc)
   from S23 S34 S52 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdot>B \<ls> C\<cdot>D \<longleftrightarrow> A\<cdiv>D \<ls> C\<cdiv>B" by (rule MMI_3bitr4d)
qed

lemma (in MMIsar0) MMI_ledivmul2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A \<lsq> C\<cdot>B"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A \<lsq> B\<cdot>C" by (rule MMI_ledivmult)
   have S2: "B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_axmulcom)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S4: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S2 S3 S4 have S5: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_syl2an)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_3adant1)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B\<cdot>C = C\<cdot>B" by (rule MMI_adantr)
   from S7 have S8: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B\<cdot>C \<longleftrightarrow> A \<lsq> C\<cdot>B" by (rule MMI_breq2d)
   from S1 S8 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A \<lsq> C\<cdot>B" by (rule MMI_bitrd)
qed

(************ 451 -460 *************************)



lemma (in MMIsar0) MMI_lemuldivt: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> A \<lsq> C\<cdiv>B"
proof -
   have S1: "(C \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdiv>B \<ls> A \<longleftrightarrow> C \<ls> A\<cdot>B" by (rule MMI_ltdivmul2t)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longleftrightarrow> 
   C \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real>" by (rule MMI_3anrev)
   from S1 S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdiv>B \<ls> A \<longleftrightarrow> C \<ls> A\<cdot>B" by (rule MMI_sylanb)
   from S3 have S4: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   \<not>(C\<cdiv>B \<ls> A) \<longleftrightarrow> \<not>(C \<ls> A\<cdot>B)" by (rule MMI_negbid)
   have S5: "A \<in> \<real> \<and> C\<cdiv>B \<in> \<real> \<longrightarrow> 
   A \<lsq> C\<cdiv>B \<longleftrightarrow> \<not>(C\<cdiv>B \<ls> A)" by (rule MMI_lenltt)
   have S6: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A \<in> \<real>" by (rule MMI_adantr)
   have S8: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S8 have S9: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_adantlr)
   have S10: "C \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_redivclt)
   from S10 have S11: "B \<in> \<real> \<and> C \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3com12)
   from S11 have S12: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3expa)
   from S9 S12 have S13: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_syldan)
   from S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> C\<cdiv>B \<in> \<real>" by (rule MMI_3adantl1)
   from S5 S7 S14 have S15: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> C\<cdiv>B \<longleftrightarrow> \<not>(C\<cdiv>B \<ls> A)" by (rule MMI_sylanc)
   have S16: "A\<cdot>B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> \<not>(C \<ls> A\<cdot>B)" by (rule MMI_lenltt)
   have S17: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A\<cdot>B \<in> \<real>" by (rule MMI_axmulrcl)
   from S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A\<cdot>B \<in> \<real>" by (rule MMI_3adant3)
   have S19: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_3simp3)
   from S16 S18 S19 have S20: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> \<not>(C \<ls> A\<cdot>B)" by (rule MMI_sylanc)
   from S20 have S21: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> \<not>(C \<ls> A\<cdot>B)" by (rule MMI_adantr)
   from S4 S15 S21 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> A \<lsq> C\<cdiv>B" by (rule MMI_3bitr4rd)
qed

lemma (in MMIsar0) MMI_lemuldiv2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> B \<lsq> C\<cdiv>A"
proof -
   have S1: "B \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_axmulcom)
   have S2: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S3: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 S3 have S4: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_syl2an)
   from S4 have S5: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_3adant3)
   from S5 have S6: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> B\<cdot>A = A\<cdot>B" by (rule MMI_adantr)
   from S6 have S7: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   B\<cdot>A \<lsq> C \<longleftrightarrow> A\<cdot>B \<lsq> C" by (rule MMI_breq1d)
   have S8: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   B\<cdot>A \<lsq> C \<longleftrightarrow> B \<lsq> C\<cdiv>A" by (rule MMI_lemuldivt)
   from S7 S8 have S9: "(B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> B \<lsq> C\<cdiv>A" by (rule MMI_bitr3d)
   from S9 have S10: "B \<in> \<real> \<and> A \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> B \<lsq> C\<cdiv>A" by (rule MMI_ex)
   from S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> B \<lsq> C\<cdiv>A" by (rule MMI_3com12)
   from S11 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<longrightarrow> 
   A\<cdot>B \<lsq> C \<longleftrightarrow> B \<lsq> C\<cdiv>A" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_ltreci: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero> \<ls> A" and
    A4: "\<zero> \<ls> B"   
   shows "A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from S1 have S2: "A \<in> \<complex>" by (rule MMI_recn)
   from A1 have S3: "A \<in> \<real>".
   from A3 have S4: "\<zero> \<ls> A".
   from S3 S4 have S5: "A \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S2 S5 have S6: "A\<cdiv>A = \<one>" by (rule MMI_divid)
   from A2 have S7: "B \<in> \<real>".
   from S7 have S8: "B \<in> \<complex>" by (rule MMI_recn)
   from A2 have S9: "B \<in> \<real>".
   from A4 have S10: "\<zero> \<ls> B".
   from S9 S10 have S11: "B \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S8 S11 have S12: "B\<cdot>(\<one>\<cdiv>B) = \<one>" by (rule MMI_recid)
   from S6 S12 have S13: "A\<cdiv>A = B\<cdot>(\<one>\<cdiv>B)" by (rule MMI_eqtr4)
   from S8 have S14: "B \<in> \<complex>" .
   from S2 have S15: "A \<in> \<complex>" .
   from S5 have S16: "A \<noteq> \<zero>" .
   from S14 S15 S16 have S17: "B\<cdiv>A = B\<cdot>(\<one>\<cdiv>A)" by (rule MMI_divrec)
   from S13 S17 have S18: "A\<cdiv>A \<ls> B\<cdiv>A \<longleftrightarrow> 
   B\<cdot>(\<one>\<cdiv>B) \<ls> B\<cdot>(\<one>\<cdiv>A)" by (rule MMI_breq12i)
   from A1 have S19: "A \<in> \<real>".
   from A2 have S20: "B \<in> \<real>".
   from A1 have S21: "A \<in> \<real>".
   from A3 have S22: "\<zero> \<ls> A".
   from S19 S20 S21 S22 have S23: "A \<ls> B \<longleftrightarrow> A\<cdiv>A \<ls> B\<cdiv>A" by (rule MMI_ltdiv1i)
   from A4 have S24: "\<zero> \<ls> B".
   from A2 have S25: "B \<in> \<real>".
   from S11 have S26: "B \<noteq> \<zero>" .
   from S25 S26 have S27: "\<one>\<cdiv>B \<in> \<real>" by (rule MMI_rereccl)
   from A1 have S28: "A \<in> \<real>".
   from S5 have S29: "A \<noteq> \<zero>" .
   from S28 S29 have S30: "\<one>\<cdiv>A \<in> \<real>" by (rule MMI_rereccl)
   from A2 have S31: "B \<in> \<real>".
   from S27 S30 S31 have S32: "\<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   B\<cdot>(\<one>\<cdiv>B) \<ls> B\<cdot>(\<one>\<cdiv>A)" by (rule MMI_ltmul2)
   from S24 S32 have S33: "\<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   B\<cdot>(\<one>\<cdiv>B) \<ls> B\<cdot>(\<one>\<cdiv>A)" by (rule MMI_ax_mp)
   from S18 S23 S33 show "A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_ltrec: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A"
proof -
   have S1: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   ( if(\<zero> \<ls> A, A, \<one>)) \<ls> B" by (rule MMI_breq1)
   have S2: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   \<one>\<cdiv>A = \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_opreq2)
   from S2 have S3: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_breq2d)
   from S1 S3 have S4: "A =  if(\<zero> \<ls> A, A, \<one>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A) \<longleftrightarrow> 
   ( if(\<zero> \<ls> A, A, \<one>)) \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_bibi12d)
   have S5: "B =  if(\<zero> \<ls> B, B, \<one>) \<longrightarrow> 
   ( if(\<zero> \<ls> A, A, \<one>)) \<ls> B \<longleftrightarrow> 
   ( if(\<zero> \<ls> A, A, \<one>)) \<ls> ( if(\<zero> \<ls> B, B, \<one>))" by (rule MMI_breq2)
   have S6: "B =  if(\<zero> \<ls> B, B, \<one>) \<longrightarrow> 
   \<one>\<cdiv>B = \<one>\<cdiv>( if(\<zero> \<ls> B, B, \<one>))" by (rule MMI_opreq2)
   from S6 have S7: "B =  if(\<zero> \<ls> B, B, \<one>) \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(\<zero> \<ls> B, B, \<one>)) \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_breq1d)
   from S5 S7 have S8: "B =  if(\<zero> \<ls> B, B, \<one>) \<longrightarrow> 
   (( if(\<zero> \<ls> A, A, \<one>)) \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))) \<longleftrightarrow> 
   ( if(\<zero> \<ls> A, A, \<one>)) \<ls> ( if(\<zero> \<ls> B, B, \<one>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(\<zero> \<ls> B, B, \<one>)) \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_bibi12d)
   from A1 have S9: "A \<in> \<real>".
   have S10: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S9 S10 have S11: " if(\<zero> \<ls> A, A, \<one>) \<in> \<real>" by (rule MMI_keepel)
   from A2 have S12: "B \<in> \<real>".
   have S13: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S12 S13 have S14: " if(\<zero> \<ls> B, B, \<one>) \<in> \<real>" by (rule MMI_keepel)
   have S15: "\<zero> \<ls> ( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_elimgt0)
   have S16: "\<zero> \<ls> ( if(\<zero> \<ls> B, B, \<one>))" by (rule MMI_elimgt0)
   from S11 S14 S15 S16 have S17: "( if(\<zero> \<ls> A, A, \<one>)) \<ls> ( if(\<zero> \<ls> B, B, \<one>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(\<zero> \<ls> B, B, \<one>)) \<ls> \<one>\<cdiv>( if(\<zero> \<ls> A, A, \<one>))" by (rule MMI_ltreci)
   from S4 S8 S17 show "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_lerec: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_ltrec)
   from A1 have S4: "A \<in> \<real>".
   from S4 have S5: "A \<in> \<complex>" by (rule MMI_recn)
   from A2 have S6: "B \<in> \<real>".
   from S6 have S7: "B \<in> \<complex>" by (rule MMI_recn)
   from S5 S7 have S8: "A \<noteq> \<zero> \<and> B \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>A = \<one>\<cdiv>B \<longleftrightarrow> A = B" by (rule MMI_rec11)
   from A1 have S9: "A \<in> \<real>".
   from S9 have S10: "\<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from A2 have S11: "B \<in> \<real>".
   from S11 have S12: "\<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from S8 S10 S12 have S13: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>A = \<one>\<cdiv>B \<longleftrightarrow> A = B" by (rule MMI_syl2an)
   have S14: "\<one>\<cdiv>A = \<one>\<cdiv>B \<longleftrightarrow> 
   \<one>\<cdiv>B = \<one>\<cdiv>A" by (rule MMI_eqcom)
   from S13 S14 have S15: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A = B \<longleftrightarrow> 
   \<one>\<cdiv>B = \<one>\<cdiv>A" by (rule MMI_syl5rbbr)
   from S3 S15 have S16: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<or> A = B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<or> \<one>\<cdiv>B = \<one>\<cdiv>A" by (rule MMI_orbi12d)
   from S12 have S17: "\<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   from A2 have S18: "B \<in> \<real>".
   from S18 have S19: "B \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_rerecclz)
   from S17 S19 have S20: "\<zero> \<ls> B \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_syl)
   from S10 have S21: "\<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" .
   from A1 have S22: "A \<in> \<real>".
   from S22 have S23: "A \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_rerecclz)
   from S21 S23 have S24: "\<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_syl)
   from S20 S24 have S25: "\<zero> \<ls> B \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>B \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_anim12i)
   from S25 have S26: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>B \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_ancoms)
   have S27: "\<one>\<cdiv>B \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<or> \<one>\<cdiv>B = \<one>\<cdiv>A" by (rule MMI_leloet)
   from S26 S27 have S28: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<or> \<one>\<cdiv>B = \<one>\<cdiv>A" by (rule MMI_syl)
   from S16 S28 have S29: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<or> A = B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_bitr4d)
   from A1 have S30: "A \<in> \<real>".
   from A2 have S31: "B \<in> \<real>".
   from S30 S31 have S32: "A \<lsq> B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_leloe)
   from S29 S32 show "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_syl5bb)
qed

lemma (in MMIsar0) MMI_lt2msq: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A1 have S3: "A \<in> \<real>".
   from S1 S2 S3 have S4: "\<zero> \<ls> A \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> A\<cdot>B" by (rule MMI_ltmul2)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from A2 have S7: "B \<in> \<real>".
   from S5 S6 S7 have S8: "\<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>B \<ls> B\<cdot>B" by (rule MMI_ltmul1)
   from S4 S8 have S9: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<and> A \<ls> B \<longleftrightarrow> 
   A\<cdot>A \<ls> A\<cdot>B \<and> A\<cdot>B \<ls> B\<cdot>B" by (rule MMI_bi2anan9)
   have S10: "A \<ls> B \<and> A \<ls> B \<longleftrightarrow> A \<ls> B" by (rule MMI_anidm)
   from S9 S10 have S11: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   A\<cdot>A \<ls> A\<cdot>B \<and> A\<cdot>B \<ls> B\<cdot>B" by (rule MMI_syl5bbr)
   from A1 have S12: "A \<in> \<real>".
   from A1 have S13: "A \<in> \<real>".
   from S12 S13 have S14: "A\<cdot>A \<in> \<real>" by (rule MMI_remulcl)
   from A1 have S15: "A \<in> \<real>".
   from A2 have S16: "B \<in> \<real>".
   from S15 S16 have S17: "A\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S18: "B \<in> \<real>".
   from A2 have S19: "B \<in> \<real>".
   from S18 S19 have S20: "B\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   from S14 S17 S20 have S21: "A\<cdot>A \<ls> A\<cdot>B \<and> A\<cdot>B \<ls> B\<cdot>B \<longrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_lttr)
   from S11 S21 have S22: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_syl6bi)
   from A2 have S23: "B \<in> \<real>".
   from A1 have S24: "A \<in> \<real>".
   from A2 have S25: "B \<in> \<real>".
   from S23 S24 S25 have S26: "\<zero> \<ls> B \<longrightarrow> 
   B \<lsq> A \<longleftrightarrow> B\<cdot>B \<lsq> B\<cdot>A" by (rule MMI_lemul2)
   from A2 have S27: "B \<in> \<real>".
   from A1 have S28: "A \<in> \<real>".
   from A1 have S29: "A \<in> \<real>".
   from S27 S28 S29 have S30: "\<zero> \<ls> A \<longrightarrow> 
   B \<lsq> A \<longleftrightarrow> B\<cdot>A \<lsq> A\<cdot>A" by (rule MMI_lemul1)
   from S26 S30 have S31: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<lsq> A \<and> B \<lsq> A \<longleftrightarrow> 
   B\<cdot>B \<lsq> B\<cdot>A \<and> B\<cdot>A \<lsq> A\<cdot>A" by (rule MMI_bi2anan9r)
   have S32: "B \<lsq> A \<and> B \<lsq> A \<longleftrightarrow> B \<lsq> A" by (rule MMI_anidm)
   from S31 S32 have S33: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<lsq> A \<longleftrightarrow> 
   B\<cdot>B \<lsq> B\<cdot>A \<and> B\<cdot>A \<lsq> A\<cdot>A" by (rule MMI_syl5bbr)
   from S20 have S34: "B\<cdot>B \<in> \<real>" .
   from A2 have S35: "B \<in> \<real>".
   from A1 have S36: "A \<in> \<real>".
   from S35 S36 have S37: "B\<cdot>A \<in> \<real>" by (rule MMI_remulcl)
   from S14 have S38: "A\<cdot>A \<in> \<real>" .
   from S34 S37 S38 have S39: "B\<cdot>B \<lsq> B\<cdot>A \<and> B\<cdot>A \<lsq> A\<cdot>A \<longrightarrow> B\<cdot>B \<lsq> A\<cdot>A" by (rule MMI_letr)
   from S33 S39 have S40: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<lsq> A \<longrightarrow> B\<cdot>B \<lsq> A\<cdot>A" by (rule MMI_syl6bi)
   from A2 have S41: "B \<in> \<real>".
   from A1 have S42: "A \<in> \<real>".
   from S41 S42 have S43: "B \<lsq> A \<longleftrightarrow> \<not>(A \<ls> B)" by (rule MMI_lenlt)
   from S20 have S44: "B\<cdot>B \<in> \<real>" .
   from S14 have S45: "A\<cdot>A \<in> \<real>" .
   from S44 S45 have S46: "B\<cdot>B \<lsq> A\<cdot>A \<longleftrightarrow> 
   \<not>(A\<cdot>A \<ls> B\<cdot>B)" by (rule MMI_lenlt)
   from S40 S43 S46 have S47: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<not>(A \<ls> B) \<longrightarrow> 
   \<not>(A\<cdot>A \<ls> B\<cdot>B)" by (rule MMI_3imtr3g)
   from S47 have S48: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdot>A \<ls> B\<cdot>B \<longrightarrow> A \<ls> B" by (rule MMI_a3d)
   from S22 S48 have S49: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_impbid)
   have S50: "\<zero> = A \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> A \<ls> B" by (rule MMI_breq1)
   from S50 have S51: "\<zero> = A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> A \<ls> B" by (rule MMI_adantr)
   have S52: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S53: "B \<in> \<real>".
   from A2 have S54: "B \<in> \<real>".
   from S52 S53 S54 have S55: "\<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> 
   B\<cdot>\<zero> \<ls> B\<cdot>B" by (rule MMI_ltmul2)
   have S56: "\<zero> = A \<longrightarrow> A\<cdot>\<zero> = A\<cdot>A" by (rule MMI_opreq2)
   from S56 have S57: "\<zero> = A \<longrightarrow> 
   A\<cdot>\<zero> \<ls> B\<cdot>B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_breq1d)
   from A2 have S58: "B \<in> \<real>".
   from S58 have S59: "B \<in> \<complex>" by (rule MMI_recn)
   from S59 have S60: "B\<cdot>\<zero> = \<zero>" by (rule MMI_mul01)
   from A1 have S61: "A \<in> \<real>".
   from S61 have S62: "A \<in> \<complex>" by (rule MMI_recn)
   from S62 have S63: "A\<cdot>\<zero> = \<zero>" by (rule MMI_mul01)
   from S60 S63 have S64: "B\<cdot>\<zero> = A\<cdot>\<zero>" by (rule MMI_eqtr4)
   from S64 have S65: "B\<cdot>\<zero> \<ls> B\<cdot>B \<longleftrightarrow> 
   A\<cdot>\<zero> \<ls> B\<cdot>B" by (rule MMI_breq1i)
   from S57 S65 have S66: "\<zero> = A \<longrightarrow> 
   B\<cdot>\<zero> \<ls> B\<cdot>B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_syl5bb)
   from S55 S66 have S67: "\<zero> = A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_sylan9bbr)
   from S51 S67 have S68: "\<zero> = A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_bitr3d)
   have S69: "\<zero> = B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> B \<lsq> A" by (rule MMI_breq1)
   from S69 have S70: "\<zero> \<ls> A \<and> \<zero> = B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> B \<lsq> A" by (rule MMI_adantl)
   have S71: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S72: "A \<in> \<real>".
   from A1 have S73: "A \<in> \<real>".
   from S71 S72 S73 have S74: "\<zero> \<ls> A \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   A\<cdot>\<zero> \<lsq> A\<cdot>A" by (rule MMI_lemul2)
   have S75: "\<zero> = B \<longrightarrow> B\<cdot>\<zero> = B\<cdot>B" by (rule MMI_opreq2)
   from S75 have S76: "\<zero> = B \<longrightarrow> 
   B\<cdot>\<zero> \<lsq> A\<cdot>A \<longleftrightarrow> B\<cdot>B \<lsq> A\<cdot>A" by (rule MMI_breq1d)
   from S63 have S77: "A\<cdot>\<zero> = \<zero>" .
   from S60 have S78: "B\<cdot>\<zero> = \<zero>" .
   from S77 S78 have S79: "A\<cdot>\<zero> = B\<cdot>\<zero>" by (rule MMI_eqtr4)
   from S79 have S80: "A\<cdot>\<zero> \<lsq> A\<cdot>A \<longleftrightarrow> 
   B\<cdot>\<zero> \<lsq> A\<cdot>A" by (rule MMI_breq1i)
   from S76 S80 have S81: "\<zero> = B \<longrightarrow> 
   A\<cdot>\<zero> \<lsq> A\<cdot>A \<longleftrightarrow> B\<cdot>B \<lsq> A\<cdot>A" by (rule MMI_syl5bb)
   from S74 S81 have S82: "\<zero> \<ls> A \<and> \<zero> = B \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> B\<cdot>B \<lsq> A\<cdot>A" by (rule MMI_sylan9bb)
   from S70 S82 have S83: "\<zero> \<ls> A \<and> \<zero> = B \<longrightarrow> 
   B \<lsq> A \<longleftrightarrow> B\<cdot>B \<lsq> A\<cdot>A" by (rule MMI_bitr3d)
   from S43 have S84: "B \<lsq> A \<longleftrightarrow> \<not>(A \<ls> B)" .
   from S46 have S85: "B\<cdot>B \<lsq> A\<cdot>A \<longleftrightarrow> 
   \<not>(A\<cdot>A \<ls> B\<cdot>B)" .
   from S83 S84 S85 have S86: "\<zero> \<ls> A \<and> \<zero> = B \<longrightarrow> 
   \<not>(A \<ls> B) \<longleftrightarrow> 
   \<not>(A\<cdot>A \<ls> B\<cdot>B)" by (rule MMI_3bitr3g)
   from S86 have S87: "\<zero> \<ls> A \<and> \<zero> = B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_con4bid)
   have S88: "\<not>(A \<ls> B) \<and> \<not>(A\<cdot>A \<ls> B\<cdot>B) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_pm5_21)
   from A2 have S89: "B \<in> \<real>".
   from S89 have S90: "\<not>(B \<ls> B)" by (rule MMI_ltnr)
   have S91: "\<zero> = B \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> B \<ls> B" by (rule MMI_breq1)
   from S91 have S92: "\<zero> = B \<longrightarrow> 
   B \<ls> B \<longleftrightarrow> \<zero> \<ls> B" by (rule MMI_bicomd)
   from S50 have S93: "\<zero> = A \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> A \<ls> B" .
   from S92 S93 have S94: "\<zero> = A \<and> \<zero> = B \<longrightarrow> 
   B \<ls> B \<longleftrightarrow> A \<ls> B" by (rule MMI_sylan9bbr)
   from S90 S94 have S95: "\<zero> = A \<and> \<zero> = B \<longrightarrow> \<not>(A \<ls> B)" by (rule MMI_mtbii)
   from S20 have S96: "B\<cdot>B \<in> \<real>" .
   from S96 have S97: "\<not>(B\<cdot>B \<ls> B\<cdot>B)" by (rule MMI_ltnr)
   from S75 have S98: "\<zero> = B \<longrightarrow> B\<cdot>\<zero> = B\<cdot>B" .
   from S98 have S99: "\<zero> = B \<longrightarrow> 
   B\<cdot>\<zero> \<ls> B\<cdot>B \<longleftrightarrow> B\<cdot>B \<ls> B\<cdot>B" by (rule MMI_breq1d)
   from S99 have S100: "\<zero> = B \<longrightarrow> 
   B\<cdot>B \<ls> B\<cdot>B \<longleftrightarrow> 
   B\<cdot>\<zero> \<ls> B\<cdot>B" by (rule MMI_bicomd)
   from S66 have S101: "\<zero> = A \<longrightarrow> 
   B\<cdot>\<zero> \<ls> B\<cdot>B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" .
   from S100 S101 have S102: "\<zero> = A \<and> \<zero> = B \<longrightarrow> 
   B\<cdot>B \<ls> B\<cdot>B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_sylan9bbr)
   from S97 S102 have S103: "\<zero> = A \<and> \<zero> = B \<longrightarrow> 
   \<not>(A\<cdot>A \<ls> B\<cdot>B)" by (rule MMI_mtbii)
   from S88 S95 S103 have S104: "\<zero> = A \<and> \<zero> = B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_sylanc)
   from S49 S68 S87 S104 have S105: "(\<zero> \<ls> A \<or> \<zero> = A) \<and> (\<zero> \<ls> B \<or> \<zero> = B) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_ccase)
   have S106: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S107: "A \<in> \<real>".
   from S106 S107 have S108: "\<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<ls> A \<or> \<zero> = A" by (rule MMI_leloe)
   have S109: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A2 have S110: "B \<in> \<real>".
   from S109 S110 have S111: "\<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<ls> B \<or> \<zero> = B" by (rule MMI_leloe)
   from S105 S108 S111 show "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_syl2anb)
qed

lemma (in MMIsar0) MMI_le2msq: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B"
proof -
   from A2 have S1: "B \<in> \<real>".
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 have S3: "\<zero> \<lsq> B \<and> \<zero> \<lsq> A \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdot>B \<ls> A\<cdot>A" by (rule MMI_lt2msq)
   from S3 have S4: "\<zero> \<lsq> B \<and> \<zero> \<lsq> A \<longrightarrow> 
   \<not>(B \<ls> A) \<longleftrightarrow> 
   \<not>(B\<cdot>B \<ls> A\<cdot>A)" by (rule MMI_negbid)
   from A1 have S5: "A \<in> \<real>".
   from A2 have S6: "B \<in> \<real>".
   from S5 S6 have S7: "A \<lsq> B \<longleftrightarrow> \<not>(B \<ls> A)" by (rule MMI_lenlt)
   from A1 have S8: "A \<in> \<real>".
   from A1 have S9: "A \<in> \<real>".
   from S8 S9 have S10: "A\<cdot>A \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S11: "B \<in> \<real>".
   from A2 have S12: "B \<in> \<real>".
   from S11 S12 have S13: "B\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   from S10 S13 have S14: "A\<cdot>A \<lsq> B\<cdot>B \<longleftrightarrow> 
   \<not>(B\<cdot>B \<ls> A\<cdot>A)" by (rule MMI_lenlt)
   from S4 S7 S14 have S15: "\<zero> \<lsq> B \<and> \<zero> \<lsq> A \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B" by (rule MMI_3bitr4g)
   from S15 show "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B" by (rule MMI_ancoms)
qed

lemma (in MMIsar0) MMI_msq11: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A\<cdot>A = B\<cdot>B \<longleftrightarrow> A = B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_lt2msq)
   from A2 have S4: "B \<in> \<real>".
   from A1 have S5: "A \<in> \<real>".
   from S4 S5 have S6: "\<zero> \<lsq> B \<and> \<zero> \<lsq> A \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdot>B \<ls> A\<cdot>A" by (rule MMI_lt2msq)
   from S6 have S7: "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ls> A \<longleftrightarrow> B\<cdot>B \<ls> A\<cdot>A" by (rule MMI_ancoms)
   from S3 S7 have S8: "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<or> B \<ls> A \<longleftrightarrow> 
   A\<cdot>A \<ls> B\<cdot>B \<or> B\<cdot>B \<ls> A\<cdot>A" by (rule MMI_orbi12d)
   from A1 have S9: "A \<in> \<real>".
   from A2 have S10: "B \<in> \<real>".
   from S9 S10 have S11: "\<not>(A = B) \<longleftrightarrow> A \<ls> B \<or> B \<ls> A" by (rule MMI_lttri2)
   from A1 have S12: "A \<in> \<real>".
   from A1 have S13: "A \<in> \<real>".
   from S12 S13 have S14: "A\<cdot>A \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S15: "B \<in> \<real>".
   from A2 have S16: "B \<in> \<real>".
   from S15 S16 have S17: "B\<cdot>B \<in> \<real>" by (rule MMI_remulcl)
   from S14 S17 have S18: "\<not>(A\<cdot>A = B\<cdot>B) \<longleftrightarrow> 
   A\<cdot>A \<ls> B\<cdot>B \<or> B\<cdot>B \<ls> A\<cdot>A" by (rule MMI_lttri2)
   from S8 S11 S18 have S19: "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   \<not>(A = B) \<longleftrightarrow> \<not>(A\<cdot>A = B\<cdot>B)" by (rule MMI_3bitr4g)
   from S19 have S20: "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A = B \<longleftrightarrow> A\<cdot>A = B\<cdot>B" by (rule MMI_con4bid)
   from S20 show "\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A\<cdot>A = B\<cdot>B \<longleftrightarrow> A = B" by (rule MMI_bicomd)
qed

lemma (in MMIsar0) MMI_ltrect: 
   shows "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B" by (rule MMI_breq1)
   have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>A = \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq2)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2d)
   from S3 S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   from S2 S6 have S7: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B = \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S11 have S12: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq1d)
   from S10 S12 have S13: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   from S9 S13 have S14: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S15 have S16: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S16 S18 have S19: "\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<ls> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_ltrec)
   from S7 S14 S19 have S20: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_dedth2h)
   from S20 have S21: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_imp)
   from S21 show "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_an4s)
qed

lemma (in MMIsar0) MMI_lerect: 
   shows "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B" by (rule MMI_breq1)
   have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>A = \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq2)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2d)
   from S3 S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   from S2 S6 have S7: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B = \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S11 have S12: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq1d)
   from S10 S12 have S13: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   from S9 S13 have S14: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S15 have S16: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S16 S18 have S19: "\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_lerec)
   from S7 S14 S19 have S20: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_dedth2h)
   from S20 have S21: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_imp)
   from S21 show "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_an4s)
qed

 (************* 461 - 470 **************************)

 lemma (in MMIsar0) MMI_lerectOLD: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B" by (rule MMI_breq1)
   have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>A = \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq2)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2d)
   from S3 S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   from S2 S6 have S7: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S8: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S8 have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B = \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq2)
   from S11 have S12: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq1d)
   from S10 S12 have S13: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   from S9 S13 have S14: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))) \<longleftrightarrow> 
   (\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>)))" by (rule MMI_imbi12d)
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S15 have S16: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S16 S18 have S19: "\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   \<one>\<cdiv>( if(B \<in> \<real>, B, \<zero>)) \<lsq> \<one>\<cdiv>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_lerec)
   from S7 S14 S19 have S20: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_dedth2h)
   from S20 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_lt2msqt: 
   shows "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B" by (rule MMI_breq1)
   have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<and> A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq12)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_anidms)
   from S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A \<ls> B\<cdot>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> B\<cdot>B" by (rule MMI_breq1d)
   from S3 S6 have S7: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> B\<cdot>B" by (rule MMI_bibi12d)
   from S2 S7 have S8: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B) \<longleftrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> B\<cdot>B)" by (rule MMI_imbi12d)
   have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S12: "B =  if(B \<in> \<real>, B, \<zero>) \<and> B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<cdot>B = ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq12)
   from S12 have S13: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<cdot>B = ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anidms)
   from S13 have S14: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> B\<cdot>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S11 S14 have S15: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> B\<cdot>B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   from S10 S15 have S16: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> B\<cdot>B) \<longleftrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S19: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S19 have S20: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S18 S20 have S21: "\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<ls> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_lt2msq)
   from S8 S16 S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_dedth2h)
   from S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_imp)
   from S23 show "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A\<cdot>A \<ls> B\<cdot>B" by (rule MMI_an4s)
qed

lemma (in MMIsar0) MMI_ltdiv2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A"
proof -
   have S1: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longleftrightarrow> 
   (A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C" by (rule MMI_an6)
   have S2: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_ltrect)
   from S2 have S3: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A" by (rule MMI_3adant3)
   have S4: "(\<one>\<cdiv>B \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_ltmul2t)
   have S5: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_rerecclt)
   from S4 S5 have S6: "(\<one>\<cdiv>B \<in> \<real> \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_syl3anl2)
   have S7: "B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_rerecclt)
   from S6 S7 have S8: "((B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_syl3anl1)
   have S9: "C \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_divrect)
   have S10: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S9 S10 have S11: "C \<in> \<complex> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_syl3an2)
   from S11 have S12: "C \<in> \<complex> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_3expb)
   from S12 have S13: "C \<in> \<complex> \<and> (B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_3adant3)
   have S14: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_divrect)
   have S15: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S14 S15 have S16: "C \<in> \<complex> \<and> A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_syl3an2)
   from S16 have S17: "C \<in> \<complex> \<and> A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3expb)
   from S17 have S18: "C \<in> \<complex> \<and> (B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3adant2)
   from S13 S18 have S19: "C \<in> \<complex> \<and> (B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B \<ls> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_breq12d)
   from S19 have S20: "(B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<complex> \<longrightarrow> 
   C\<cdiv>B \<ls> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3coml)
   have S21: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S20 S21 have S22: "(B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<real> \<longrightarrow> 
   C\<cdiv>B \<ls> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_syl3an3)
   from S22 have S23: "((B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   C\<cdiv>B \<ls> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<ls> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_adantr)
   from S8 S23 have S24: "((B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_bitr4d)
   from S24 have S25: "(B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> (A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_ex)
   from S25 have S26: "(A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> (B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_3com12)
   from S26 have S27: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_3exp)
   from S27 have S28: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> 
   B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_imp4a)
   from S28 have S29: "(A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> (B \<in> \<real> \<and> B \<noteq> \<zero>) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_3imp)
   have S30: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_26)
   have S31: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S30 S31 have S32: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<in> \<real> \<and> B \<noteq> \<zero>" by (rule MMI_jca)
   from S29 S32 have S33: "(A \<in> \<real> \<and> A \<noteq> \<zero>) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_syl3an2)
   have S34: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   have S35: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S34 S35 have S36: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<in> \<real> \<and> A \<noteq> \<zero>" by (rule MMI_jca)
   from S33 S36 have S37: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>A \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_syl3an1)
   from S3 S37 have S38: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_bitrd)
   from S1 S38 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> C\<cdiv>B \<ls> C\<cdiv>A" by (rule MMI_sylbi)
qed

lemma (in MMIsar0) MMI_ltrec1t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>A \<ls> B \<longleftrightarrow> \<one>\<cdiv>B \<ls> A"
proof -
   have S1: "(\<one>\<cdiv>A \<in> \<real> \<and> \<zero> \<ls> \<one>\<cdiv>A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>(\<one>\<cdiv>A)" by (rule MMI_ltrect)
   have S2: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S3: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_rerecclt)
   from S2 S3 have S4: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_syldan)
   have S5: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_recgt0t)
   from S4 S5 have S6: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>A \<in> \<real> \<and> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_jca)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>A \<in> \<real> \<and> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_ad2ant2r)
   have S8: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<in> \<real> \<and> \<zero> \<ls> B" by (rule MMI_id)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<in> \<real> \<and> \<zero> \<ls> B" by (rule MMI_ad2ant2l)
   from S1 S7 S9 have S10: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>A \<ls> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>(\<one>\<cdiv>A)" by (rule MMI_sylanc)
   have S11: "A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>A) = A" by (rule MMI_recrect)
   have S12: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S12 have S13: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<in> \<complex>" by (rule MMI_adantr)
   from S2 have S14: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" .
   from S11 S13 S14 have S15: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>A) = A" by (rule MMI_sylanc)
   from S15 have S16: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>A) = A" by (rule MMI_ad2ant2r)
   from S16 have S17: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>B \<ls> \<one>\<cdiv>(\<one>\<cdiv>A) \<longleftrightarrow> \<one>\<cdiv>B \<ls> A" by (rule MMI_breq2d)
   from S10 S17 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>A \<ls> B \<longleftrightarrow> \<one>\<cdiv>B \<ls> A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lerec2t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> \<one>\<cdiv>B \<longleftrightarrow> B \<lsq> \<one>\<cdiv>A"
proof -
   have S1: "(A \<in> \<real> \<and> \<one>\<cdiv>B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> \<one>\<cdiv>B \<longrightarrow> 
   A \<lsq> \<one>\<cdiv>B \<longleftrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>B) \<lsq> \<one>\<cdiv>A" by (rule MMI_lerectOLD)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> A \<in> \<real>" by (rule MMI_adantr)
   have S4: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S5: "B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_rerecclt)
   from S4 S5 have S6: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_syldan)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_ad2ant2l)
   from S3 S7 have S8: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<in> \<real> \<and> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_jca)
   have S9: "\<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A" by (rule MMI_pm3_26)
   from S9 have S10: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A" by (rule MMI_adantl)
   have S11: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>B" by (rule MMI_recgt0t)
   from S11 have S12: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>B" by (rule MMI_ad2ant2l)
   from S10 S12 have S13: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> \<one>\<cdiv>B" by (rule MMI_jca)
   from S1 S8 S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> \<one>\<cdiv>B \<longleftrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>B) \<lsq> \<one>\<cdiv>A" by (rule MMI_sylanc)
   have S15: "B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>B) = B" by (rule MMI_recrect)
   have S16: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S16 have S17: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<complex>" by (rule MMI_adantr)
   from S4 have S18: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   from S15 S17 S18 have S19: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>B) = B" by (rule MMI_sylanc)
   from S19 have S20: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>B) = B" by (rule MMI_ad2ant2l)
   from S20 have S21: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>(\<one>\<cdiv>B) \<lsq> \<one>\<cdiv>A \<longleftrightarrow> B \<lsq> \<one>\<cdiv>A" by (rule MMI_breq1d)
   from S14 S21 show "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> \<one>\<cdiv>B \<longleftrightarrow> B \<lsq> \<one>\<cdiv>A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_ledivdivt: 
   shows "((A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B) \<and> (C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdiv>B \<lsq> C\<cdiv>D \<longleftrightarrow> D\<cdiv>C \<lsq> B\<cdiv>A"
proof -
   have S1: "(A\<cdiv>B \<in> \<real> \<and> C\<cdiv>D \<in> \<real>) \<and> \<zero> \<ls> A\<cdiv>B \<and> \<zero> \<ls> C\<cdiv>D \<longrightarrow> 
   A\<cdiv>B \<lsq> C\<cdiv>D \<longleftrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) \<lsq> \<one>\<cdiv>(A\<cdiv>B)" by (rule MMI_lerectOLD)
   from S1 have S2: "(A\<cdiv>B \<in> \<real> \<and> \<zero> \<ls> A\<cdiv>B) \<and> C\<cdiv>D \<in> \<real> \<and> \<zero> \<ls> C\<cdiv>D \<longrightarrow> 
   A\<cdiv>B \<lsq> C\<cdiv>D \<longleftrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) \<lsq> \<one>\<cdiv>(A\<cdiv>B)" by (rule MMI_an4s)
   have S3: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_redivclt)
   from S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3expb)
   have S5: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_26)
   have S6: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S5 S6 have S7: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<in> \<real> \<and> B \<noteq> \<zero>" by (rule MMI_jca)
   from S4 S7 have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_sylan2)
   from S8 have S9: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_adantlr)
   have S10: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_divgt0t)
   from S10 have S11: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> A\<cdiv>B" by (rule MMI_an4s)
   from S9 S11 have S12: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<in> \<real> \<and> \<zero> \<ls> A\<cdiv>B" by (rule MMI_jca)
   have S13: "C \<in> \<real> \<and> D \<in> \<real> \<and> D \<noteq> \<zero> \<longrightarrow> C\<cdiv>D \<in> \<real>" by (rule MMI_redivclt)
   from S13 have S14: "C \<in> \<real> \<and> D \<in> \<real> \<and> D \<noteq> \<zero> \<longrightarrow> C\<cdiv>D \<in> \<real>" by (rule MMI_3expb)
   have S15: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> D \<in> \<real>" by (rule MMI_pm3_26)
   have S16: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> D \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S15 S16 have S17: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   D \<in> \<real> \<and> D \<noteq> \<zero>" by (rule MMI_jca)
   from S14 S17 have S18: "C \<in> \<real> \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> C\<cdiv>D \<in> \<real>" by (rule MMI_sylan2)
   from S18 have S19: "(C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> C\<cdiv>D \<in> \<real>" by (rule MMI_adantlr)
   have S20: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> C\<cdiv>D" by (rule MMI_divgt0t)
   from S20 have S21: "(C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> C\<cdiv>D" by (rule MMI_an4s)
   from S19 S21 have S22: "(C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   C\<cdiv>D \<in> \<real> \<and> \<zero> \<ls> C\<cdiv>D" by (rule MMI_jca)
   from S2 S12 S22 have S23: "((A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B) \<and> (C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdiv>B \<lsq> C\<cdiv>D \<longleftrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) \<lsq> \<one>\<cdiv>(A\<cdiv>B)" by (rule MMI_syl2an)
   have S24: "(C \<in> \<complex> \<and> D \<in> \<complex>) \<and> C \<noteq> \<zero> \<and> D \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) = D\<cdiv>C" by (rule MMI_recdivt)
   from S24 have S25: "(C \<in> \<complex> \<and> C \<noteq> \<zero>) \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) = D\<cdiv>C" by (rule MMI_an4s)
   have S26: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S26 have S27: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<in> \<complex>" by (rule MMI_adantr)
   have S28: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S27 S28 have S29: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   C \<in> \<complex> \<and> C \<noteq> \<zero>" by (rule MMI_jca)
   have S30: "D \<in> \<real> \<longrightarrow> D \<in> \<complex>" by (rule MMI_recnt)
   from S30 have S31: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> D \<in> \<complex>" by (rule MMI_adantr)
   from S16 have S32: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> D \<noteq> \<zero>" .
   from S31 S32 have S33: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   D \<in> \<complex> \<and> D \<noteq> \<zero>" by (rule MMI_jca)
   from S25 S29 S33 have S34: "(C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) = D\<cdiv>C" by (rule MMI_syl2an)
   have S35: "(A \<in> \<complex> \<and> B \<in> \<complex>) \<and> A \<noteq> \<zero> \<and> B \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>(A\<cdiv>B) = B\<cdiv>A" by (rule MMI_recdivt)
   from S35 have S36: "(A \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> 
   \<one>\<cdiv>(A\<cdiv>B) = B\<cdiv>A" by (rule MMI_an4s)
   have S37: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S37 have S38: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<in> \<complex>" by (rule MMI_adantr)
   have S39: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S38 S39 have S40: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<in> \<complex> \<and> A \<noteq> \<zero>" by (rule MMI_jca)
   have S41: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S41 have S42: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<complex>" by (rule MMI_adantr)
   from S6 have S43: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   from S42 S43 have S44: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<in> \<complex> \<and> B \<noteq> \<zero>" by (rule MMI_jca)
   from S36 S40 S44 have S45: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   \<one>\<cdiv>(A\<cdiv>B) = B\<cdiv>A" by (rule MMI_syl2an)
   from S34 S45 have S46: "((A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B) \<and> (C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   \<one>\<cdiv>(C\<cdiv>D) \<lsq> \<one>\<cdiv>(A\<cdiv>B) \<longleftrightarrow> D\<cdiv>C \<lsq> B\<cdiv>A" by (rule MMI_breqan12rd)
   from S23 S46 show "((A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B) \<and> (C \<in> \<real> \<and> \<zero> \<ls> C) \<and> D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> 
   A\<cdiv>B \<lsq> C\<cdiv>D \<longleftrightarrow> D\<cdiv>C \<lsq> B\<cdiv>A" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_lediv2t: 
   shows "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdiv>B \<lsq> C\<cdiv>A"
proof -
   have S1: "(\<one>\<cdiv>B \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<lsq> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_lemul2t)
   have S2: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S3: "B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_rerecclt)
   from S2 S3 have S4: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_syldan)
   from S4 have S5: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> \<one>\<cdiv>B \<in> \<real>" by (rule MMI_3ad2ant2)
   have S6: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S7: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_rerecclt)
   from S6 S7 have S8: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_syldan)
   from S8 have S9: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_3ad2ant1)
   have S10: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<in> \<real>" by (rule MMI_pm3_26)
   from S10 have S11: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<in> \<real>" by (rule MMI_3ad2ant3)
   from S5 S9 S11 have S12: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3jca)
   have S13: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> \<zero> \<ls> C" by (rule MMI_pm3_27)
   from S13 have S14: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> \<zero> \<ls> C" by (rule MMI_3ad2ant3)
   from S1 S12 S14 have S15: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<lsq> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_sylanc)
   have S16: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_lerectOLD)
   from S16 have S17: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_an4s)
   from S17 have S18: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   \<one>\<cdiv>B \<lsq> \<one>\<cdiv>A" by (rule MMI_3adant3)
   have S19: "C \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_divrect)
   from S19 have S20: "C \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_3expb)
   have S21: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   have S22: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S22 have S23: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<complex>" by (rule MMI_adantr)
   from S2 have S24: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   from S23 S24 have S25: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   B \<in> \<complex> \<and> B \<noteq> \<zero>" by (rule MMI_jca)
   from S20 S21 S25 have S26: "C \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_syl2an)
   from S26 have S27: "C \<in> \<real> \<and> (A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdiv>B = C\<cdot>(\<one>\<cdiv>B)" by (rule MMI_3adant2)
   have S28: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_divrect)
   from S28 have S29: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3expb)
   from S21 have S30: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" .
   have S31: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S31 have S32: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<in> \<complex>" by (rule MMI_adantr)
   from S6 have S33: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" .
   from S32 S33 have S34: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<in> \<complex> \<and> A \<noteq> \<zero>" by (rule MMI_jca)
   from S29 S30 S34 have S35: "C \<in> \<real> \<and> A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_syl2an)
   from S35 have S36: "C \<in> \<real> \<and> (A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdiv>A = C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3adant3)
   from S27 S36 have S37: "C \<in> \<real> \<and> (A \<in> \<real> \<and> \<zero> \<ls> A) \<and> B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> 
   C\<cdiv>B \<lsq> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<lsq> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_breq12d)
   from S37 have S38: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<longrightarrow> 
   C\<cdiv>B \<lsq> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<lsq> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3coml)
   from S38 have S39: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   C\<cdiv>B \<lsq> C\<cdiv>A \<longleftrightarrow> 
   C\<cdot>(\<one>\<cdiv>B) \<lsq> C\<cdot>(\<one>\<cdiv>A)" by (rule MMI_3adant3r)
   from S15 S18 S39 show "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> (B \<in> \<real> \<and> \<zero> \<ls> B) \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> C\<cdiv>B \<lsq> C\<cdiv>A" by (rule MMI_3bitr4d)
qed

lemma (in MMIsar0) MMI_ltdiv23t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B"
proof -
   have S1: "(A\<cdiv>B \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<ls> C\<cdot>B" by (rule MMI_ltmul1t)
   have S2: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_adantll)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_redivclt)
   from S4 have S5: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3expa)
   from S3 S5 have S6: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_syldan)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3adantl3)
   have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_3simp3)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> C \<in> \<real>" by (rule MMI_adantr)
   have S10: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S10 have S11: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<real>" by (rule MMI_adantr)
   from S7 S9 S11 have S12: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_3jca)
   have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_pm3_27)
   from S1 S12 S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<ls> C\<cdot>B" by (rule MMI_sylanc)
   from S14 have S15: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<ls> C\<cdot>B" by (rule MMI_adantrr)
   from S3 have S16: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   have S17: "B \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_divcan1t)
   from S17 have S18: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3com12)
   from S18 have S19: "(A \<in> \<complex> \<and> B \<in> \<complex>) \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3expa)
   have S20: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S21: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S20 S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_anim12i)
   from S19 S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_sylan)
   from S16 S23 have S24: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_syldan)
   from S24 have S25: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3adantl3)
   from S25 have S26: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_adantrr)
   from S26 have S27: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   (A\<cdiv>B)\<cdot>B \<ls> C\<cdot>B \<longleftrightarrow> A \<ls> C\<cdot>B" by (rule MMI_breq1d)
   have S28: "(A \<in> \<real> \<and> C\<cdot>B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> C\<cdot>B \<longleftrightarrow> 
   A\<cdiv>C \<ls> C\<cdot>B\<cdiv>C" by (rule MMI_ltdiv1t)
   have S29: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   have S30: "C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_axmulrcl)
   from S30 have S31: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_ancoms)
   from S31 have S32: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_3adant1)
   from S8 have S33: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" .
   from S29 S32 S33 have S34: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> C\<cdot>B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3jca)
   from S28 S34 have S35: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> C\<cdot>B \<longleftrightarrow> 
   A\<cdiv>C \<ls> C\<cdot>B\<cdiv>C" by (rule MMI_sylan)
   have S36: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S36 have S37: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_adantll)
   have S38: "C \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_divcan3t)
   from S21 have S39: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" .
   from S38 S39 have S40: "C \<in> \<complex> \<and> B \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syl3an2)
   have S41: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S40 S41 have S42: "C \<in> \<real> \<and> B \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syl3an1)
   from S42 have S43: "B \<in> \<real> \<and> C \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3com12)
   from S43 have S44: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3expa)
   from S37 S44 have S45: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syldan)
   from S45 have S46: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3adantl1)
   from S46 have S47: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>C \<ls> C\<cdot>B\<cdiv>C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_breq2d)
   from S35 S47 have S48: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> C\<cdot>B \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_bitrd)
   from S48 have S49: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<ls> C\<cdot>B \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_adantrl)
   from S15 S27 S49 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_3bitrd)
qed

lemma (in MMIsar0) MMI_lediv23t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A\<cdiv>C \<lsq> B"
proof -
   have S1: "(A\<cdiv>B \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B" by (rule MMI_lemul1t)
   have S2: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_adantll)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_redivclt)
   from S4 have S5: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3expa)
   from S3 S5 have S6: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_syldan)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3adantl3)
   have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_3simp3)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> C \<in> \<real>" by (rule MMI_adantr)
   have S10: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S10 have S11: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<real>" by (rule MMI_adantr)
   from S7 S9 S11 have S12: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_3jca)
   have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_pm3_27)
   from S1 S12 S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B" by (rule MMI_sylanc)
   from S14 have S15: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B" by (rule MMI_adantrr)
   from S3 have S16: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   have S17: "B \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_divcan1t)
   from S17 have S18: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3com12)
   from S18 have S19: "(A \<in> \<complex> \<and> B \<in> \<complex>) \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3expa)
   have S20: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S21: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S20 S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_anim12i)
   from S19 S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_sylan)
   from S16 S23 have S24: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_syldan)
   from S24 have S25: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3adantl3)
   from S25 have S26: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_adantrr)
   from S26 have S27: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B \<longleftrightarrow> A \<lsq> C\<cdot>B" by (rule MMI_breq1d)
   have S28: "(A \<in> \<real> \<and> C\<cdot>B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> 
   A\<cdiv>C \<lsq> C\<cdot>B\<cdiv>C" by (rule MMI_lediv1t)
   have S29: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   have S30: "C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_axmulrcl)
   from S30 have S31: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_ancoms)
   from S31 have S32: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_3adant1)
   from S8 have S33: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" .
   from S29 S32 S33 have S34: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> C\<cdot>B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3jca)
   from S28 S34 have S35: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> 
   A\<cdiv>C \<lsq> C\<cdot>B\<cdiv>C" by (rule MMI_sylan)
   have S36: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S36 have S37: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_adantll)
   have S38: "C \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_divcan3t)
   from S21 have S39: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" .
   from S38 S39 have S40: "C \<in> \<complex> \<and> B \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syl3an2)
   have S41: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S40 S41 have S42: "C \<in> \<real> \<and> B \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syl3an1)
   from S42 have S43: "B \<in> \<real> \<and> C \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3com12)
   from S43 have S44: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3expa)
   from S37 S44 have S45: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syldan)
   from S45 have S46: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3adantl1)
   from S46 have S47: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>C \<lsq> C\<cdot>B\<cdiv>C \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_breq2d)
   from S35 S47 have S48: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_bitrd)
   from S48 have S49: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_adantrl)
   from S15 S27 S49 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_3bitrd)
qed

lemma (in MMIsar0) MMI_ltdiv23: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from S1 S2 S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3pm3_2i)
   have S5: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_ltdiv23t)
   from S4 S5 show "\<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_mpan)
qed

(************ 471 - 480 *****************)
(*lemma (in MMIsar0) MMI_lediv23t: 
   shows "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A\<cdiv>C \<lsq> B"
proof -
   have S1: "(A\<cdiv>B \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B" by (rule MMI_lemul1t)
   have S2: "B \<in> \<real> \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S2 have S3: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_adantll)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_redivclt)
   from S4 have S5: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3expa)
   from S3 S5 have S6: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_syldan)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> A\<cdiv>B \<in> \<real>" by (rule MMI_3adantl3)
   have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_3simp3)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> C \<in> \<real>" by (rule MMI_adantr)
   have S10: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S10 have S11: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<in> \<real>" by (rule MMI_adantr)
   from S7 S9 S11 have S12: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<in> \<real> \<and> C \<in> \<real> \<and> B \<in> \<real>" by (rule MMI_3jca)
   have S13: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> \<zero> \<ls> B" by (rule MMI_pm3_27)
   from S1 S12 S13 have S14: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B" by (rule MMI_sylanc)
   from S14 have S15: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B" by (rule MMI_adantrr)
   from S3 have S16: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> B \<noteq> \<zero>" .
   have S17: "B \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_divcan1t)
   from S17 have S18: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3com12)
   from S18 have S19: "(A \<in> \<complex> \<and> B \<in> \<complex>) \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3expa)
   have S20: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S21: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S20 S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_anim12i)
   from S19 S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> B \<noteq> \<zero> \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_sylan)
   from S16 S23 have S24: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_syldan)
   from S24 have S25: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_3adantl3)
   from S25 have S26: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> (A\<cdiv>B)\<cdot>B = A" by (rule MMI_adantrr)
   from S26 have S27: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   (A\<cdiv>B)\<cdot>B \<lsq> C\<cdot>B \<longleftrightarrow> A \<lsq> C\<cdot>B" by (rule MMI_breq1d)
   have S28: "(A \<in> \<real> \<and> C\<cdot>B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> 
   A\<cdiv>C \<lsq> C\<cdot>B\<cdiv>C" by (rule MMI_lediv1t)
   have S29: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   have S30: "C \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_axmulrcl)
   from S30 have S31: "B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_ancoms)
   from S31 have S32: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C\<cdot>B \<in> \<real>" by (rule MMI_3adant1)
   from S8 have S33: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" .
   from S29 S32 S33 have S34: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<in> \<real> \<and> C\<cdot>B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3jca)
   from S28 S34 have S35: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> 
   A\<cdiv>C \<lsq> C\<cdot>B\<cdiv>C" by (rule MMI_sylan)
   have S36: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S36 have S37: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_adantll)
   have S38: "C \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_divcan3t)
   from S21 have S39: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" .
   from S38 S39 have S40: "C \<in> \<complex> \<and> B \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syl3an2)
   have S41: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S40 S41 have S42: "C \<in> \<real> \<and> B \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syl3an1)
   from S42 have S43: "B \<in> \<real> \<and> C \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3com12)
   from S43 have S44: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> C \<noteq> \<zero> \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3expa)
   from S37 S44 have S45: "(B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_syldan)
   from S45 have S46: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> C\<cdot>B\<cdiv>C = B" by (rule MMI_3adantl1)
   from S46 have S47: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>C \<lsq> C\<cdot>B\<cdiv>C \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_breq2d)
   from S35 S47 have S48: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_bitrd)
   from S48 have S49: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A \<lsq> C\<cdot>B \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_adantrl)
   from S15 S27 S49 show "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<lsq> C \<longleftrightarrow> A\<cdiv>C \<lsq> B" by (rule MMI_3bitrd)
qed

lemma (in MMIsar0) MMI_ltdiv23: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from A3 have S3: "C \<in> \<real>".
   from S1 S2 S3 have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>" by (rule MMI_3pm3_2i)
   have S5: "(A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real>) \<and> \<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_ltdiv23t)
   from S4 S5 show "\<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_mpan)
qed*)

lemma (in MMIsar0) MMI_lediv12it: 
   shows "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> A\<cdiv>D \<lsq> B\<cdiv>C"
proof -
   have S1: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (\<one>\<cdiv>D \<in> \<real> \<and> \<one>\<cdiv>C \<in> \<real>) \<and> \<zero> \<lsq> \<one>\<cdiv>D \<and> \<one>\<cdiv>D \<lsq> \<one>\<cdiv>C \<longrightarrow> 
   A\<cdot>(\<one>\<cdiv>D) \<lsq> B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_lemul12it)
   have S2: "D \<in> \<real> \<and> D \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>D \<in> \<real>" by (rule MMI_rerecclt)
   have S3: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> D \<in> \<real>" by (rule MMI_pm3_27)
   from S3 have S4: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<in> \<real>" by (rule MMI_adantr)
   have S5: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> D \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S4 have S6: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<in> \<real>" .
   have S7: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S8: "\<zero> \<in> \<real> \<and> C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> D" by (rule MMI_ltletrt)
   from S7 S8 have S9: "C \<in> \<real> \<and> D \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> D" by (rule MMI_mp3an1)
   from S9 have S10: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> D" by (rule MMI_imp)
   from S5 S6 S10 have S11: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<noteq> \<zero>" by (rule MMI_sylanc)
   from S2 S4 S11 have S12: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<one>\<cdiv>D \<in> \<real>" by (rule MMI_sylanc)
   have S13: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S14: "C \<in> \<real> \<and> C \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>C \<in> \<real>" by (rule MMI_rerecclt)
   from S13 S14 have S15: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> \<one>\<cdiv>C \<in> \<real>" by (rule MMI_syldan)
   from S15 have S16: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<one>\<cdiv>C \<in> \<real>" by (rule MMI_ad2ant2r)
   from S12 S16 have S17: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   \<one>\<cdiv>D \<in> \<real> \<and> \<one>\<cdiv>C \<in> \<real>" by (rule MMI_jca)
   have S18: "D \<in> \<real> \<and> \<zero> \<ls> D \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>D" by (rule MMI_recgt0t)
   from S4 have S19: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<in> \<real>" .
   from S10 have S20: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> D" .
   from S18 S19 S20 have S21: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>D" by (rule MMI_sylanc)
   have S22: "\<zero> \<in> \<real> \<and> \<one>\<cdiv>D \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>D \<longrightarrow> \<zero> \<lsq> \<one>\<cdiv>D" by (rule MMI_ltlet)
   have S23: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S23 have S24: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<in> \<real>" by (rule MMI_a1i)
   from S12 have S25: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<one>\<cdiv>D \<in> \<real>" .
   from S22 S24 S25 have S26: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>D \<longrightarrow> \<zero> \<lsq> \<one>\<cdiv>D" by (rule MMI_sylanc)
   from S21 S26 have S27: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<lsq> \<one>\<cdiv>D" by (rule MMI_mpd)
   have S28: "\<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> C \<lsq> D" by (rule MMI_pm3_27)
   from S28 have S29: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> C \<lsq> D" by (rule MMI_adantl)
   have S30: "\<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> C" by (rule MMI_pm3_26)
   from S30 have S31: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> C" by (rule MMI_adantl)
   from S10 have S32: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> \<zero> \<ls> D" .
   from S31 S32 have S33: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   \<zero> \<ls> C \<and> \<zero> \<ls> D" by (rule MMI_jca)
   have S34: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> \<zero> \<ls> D \<longrightarrow> 
   C \<lsq> D \<longleftrightarrow> 
   \<one>\<cdiv>D \<lsq> \<one>\<cdiv>C" by (rule MMI_lerectOLD)
   from S33 S34 have S35: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   C \<lsq> D \<longleftrightarrow> 
   \<one>\<cdiv>D \<lsq> \<one>\<cdiv>C" by (rule MMI_syldan)
   from S29 S35 have S36: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   \<one>\<cdiv>D \<lsq> \<one>\<cdiv>C" by (rule MMI_mpbid)
   from S27 S36 have S37: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   \<zero> \<lsq> \<one>\<cdiv>D \<and> \<one>\<cdiv>D \<lsq> \<one>\<cdiv>C" by (rule MMI_jca)
   from S17 S37 have S38: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   (\<one>\<cdiv>D \<in> \<real> \<and> \<one>\<cdiv>C \<in> \<real>) \<and> \<zero> \<lsq> \<one>\<cdiv>D \<and> \<one>\<cdiv>D \<lsq> \<one>\<cdiv>C" by (rule MMI_jca)
   from S1 S38 have S39: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   A\<cdot>(\<one>\<cdiv>D) \<lsq> B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_sylan2)
   have S40: "A \<in> \<complex> \<and> D \<in> \<complex> \<and> D \<noteq> \<zero> \<longrightarrow> 
   A\<cdiv>D = A\<cdot>(\<one>\<cdiv>D)" by (rule MMI_divrect)
   have S41: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S41 have S42: "A \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> A \<in> \<complex>" by (rule MMI_adantr)
   have S43: "D \<in> \<real> \<longrightarrow> D \<in> \<complex>" by (rule MMI_recnt)
   from S43 have S44: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<in> \<complex>" by (rule MMI_ad2antlr)
   from S44 have S45: "A \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<in> \<complex>" by (rule MMI_adantl)
   from S11 have S46: "(C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<noteq> \<zero>" .
   from S46 have S47: "A \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> D \<noteq> \<zero>" by (rule MMI_adantl)
   from S40 S42 S45 S47 have S48: "A \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   A\<cdiv>D = A\<cdot>(\<one>\<cdiv>D)" by (rule MMI_syl3anc)
   from S48 have S49: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   A\<cdiv>D = A\<cdot>(\<one>\<cdiv>D)" by (rule MMI_adantlr)
   from S49 have S50: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   A\<cdiv>D = A\<cdot>(\<one>\<cdiv>D)" by (rule MMI_adantlr)
   have S51: "B \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> \<longrightarrow> 
   B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_divrect)
   have S52: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S52 have S53: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> B \<in> \<complex>" by (rule MMI_adantr)
   have S54: "C \<in> \<real> \<longrightarrow> C \<in> \<complex>" by (rule MMI_recnt)
   from S54 have S55: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<in> \<complex>" by (rule MMI_ad2antrl)
   from S13 have S56: "C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" .
   from S56 have S57: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> C \<noteq> \<zero>" by (rule MMI_adantl)
   from S51 S53 S55 S57 have S58: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<longrightarrow> 
   B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_syl3anc)
   from S58 have S59: "B \<in> \<real> \<and> C \<in> \<real> \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_adantrrr)
   from S59 have S60: "B \<in> \<real> \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_adantrlr)
   from S60 have S61: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_adantll)
   from S61 have S62: "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> 
   B\<cdiv>C = B\<cdot>(\<one>\<cdiv>C)" by (rule MMI_adantlr)
   from S39 S50 S62 show "((A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> A \<lsq> B) \<and> (C \<in> \<real> \<and> D \<in> \<real>) \<and> \<zero> \<ls> C \<and> C \<lsq> D \<longrightarrow> A\<cdiv>D \<lsq> B\<cdiv>C" by auto (*(rule MMI_3brtr4d)*)
qed

lemma (in MMIsar0) MMI_reclt1t: 
   shows "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<ls> \<one> \<longleftrightarrow> \<one> \<ls> \<one>\<cdiv>A"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 have S3: "\<one> \<in> \<real> \<and> \<zero> \<ls> \<one>" by (rule MMI_pm3_2i)
   have S4: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> \<one> \<in> \<real> \<and> \<zero> \<ls> \<one> \<longrightarrow> 
   A \<ls> \<one> \<longleftrightarrow> 
   \<one>\<cdiv>\<one> \<ls> \<one>\<cdiv>A" by (rule MMI_ltrect)
   from S3 S4 have S5: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<ls> \<one> \<longleftrightarrow> 
   \<one>\<cdiv>\<one> \<ls> \<one>\<cdiv>A" by (rule MMI_mpan2)
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 have S7: "\<one>\<cdiv>\<one> = \<one>" by (rule MMI_div1)
   from S7 have S8: "\<one>\<cdiv>\<one> \<ls> \<one>\<cdiv>A \<longleftrightarrow> \<one> \<ls> \<one>\<cdiv>A" by (rule MMI_breq1i)
   from S5 S8 show "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<ls> \<one> \<longleftrightarrow> \<one> \<ls> \<one>\<cdiv>A" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_recgt1t: 
   shows "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<one>\<cdiv>A \<ls> \<one>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 have S3: "\<one> \<in> \<real> \<and> \<zero> \<ls> \<one>" by (rule MMI_pm3_2i)
   have S4: "(\<one> \<in> \<real> \<and> \<zero> \<ls> \<one>) \<and> A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> 
   \<one>\<cdiv>A \<ls> \<one>\<cdiv>\<one>" by (rule MMI_ltrect)
   from S3 S4 have S5: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> 
   \<one>\<cdiv>A \<ls> \<one>\<cdiv>\<one>" by (rule MMI_mpan)
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 have S7: "\<one>\<cdiv>\<one> = \<one>" by (rule MMI_div1)
   from S7 have S8: "\<one>\<cdiv>A \<ls> \<one>\<cdiv>\<one> \<longleftrightarrow> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_breq2i)
   from S5 S8 show "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_recgt1it: 
   shows "A \<in> \<real> \<and> \<one> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>A \<and> \<one>\<cdiv>A \<ls> \<one>"
proof -
   have S1: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S2: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S4: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_axlttrn)
   from S2 S3 S4 have S5: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mp3an12)
   from S1 S5 have S6: "A \<in> \<real> \<longrightarrow> 
   \<one> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mpani)
   from S6 have S7: "A \<in> \<real> \<and> \<one> \<ls> A \<longrightarrow> 
   A \<in> \<real> \<and> \<zero> \<ls> A" by (rule MMI_imdistani)
   have S8: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_recgt0t)
   from S7 S8 have S9: "A \<in> \<real> \<and> \<one> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_syl)
   have S10: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_recgt1t)
   from S10 have S11: "(A \<in> \<real> \<and> \<zero> \<ls> A) \<and> \<one> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_biimpa)
   from S7 have S12: "A \<in> \<real> \<and> \<one> \<ls> A \<longrightarrow> 
   A \<in> \<real> \<and> \<zero> \<ls> A" .
   from S11 S12 have S13: "(A \<in> \<real> \<and> \<one> \<ls> A) \<and> \<one> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_sylan)
   from S13 have S14: "A \<in> \<real> \<and> \<one> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_anabss3)
   from S9 S14 show "A \<in> \<real> \<and> \<one> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>A \<and> \<one>\<cdiv>A \<ls> \<one>" by (rule MMI_jca)
qed

lemma (in MMIsar0) MMI_recp1lt1: 
   shows "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<ls> \<one>"
proof -
   have S1: "A \<in> \<real> \<longrightarrow> A \<ls> A \<ca> \<one>" by (rule MMI_ltp1t)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S3: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S4: "A \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
   A \<ca> \<one> = \<one> \<ca> A" by (rule MMI_axaddcom)
   from S3 S4 have S5: "A \<in> \<complex> \<longrightarrow> 
   A \<ca> \<one> = \<one> \<ca> A" by (rule MMI_mpan2)
   from S2 S5 have S6: "A \<in> \<real> \<longrightarrow> 
   A \<ca> \<one> = \<one> \<ca> A" by (rule MMI_syl)
   from S1 S6 have S7: "A \<in> \<real> \<longrightarrow> A \<ls> \<one> \<ca> A" by (rule MMI_breqtrd)
   from S7 have S8: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> A \<ls> \<one> \<ca> A" by (rule MMI_adantr)
   have S9: "\<one> \<ca> A \<in> \<complex> \<and> A \<in> \<complex> \<and> \<one> \<ca> A \<noteq> \<zero> \<longrightarrow> 
   (A\<cdiv>(\<one> \<ca> A))\<cdot>(\<one> \<ca> A) = A" by (rule MMI_divcan1t)
   have S10: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S11: "\<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> \<one> \<ca> A \<in> \<real>" by (rule MMI_axaddrcl)
   from S10 S11 have S12: "A \<in> \<real> \<longrightarrow> \<one> \<ca> A \<in> \<real>" by (rule MMI_mpan)
   from S12 have S13: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<one> \<ca> A \<in> \<real>" by (rule MMI_adantr)
   from S13 have S14: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   \<one> \<ca> A \<in> \<complex>" by (rule MMI_recnd)
   from S2 have S15: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" .
   from S15 have S16: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> A \<in> \<complex>" by (rule MMI_adantr)
   have S17: "\<one> \<ca> A \<in> \<real> \<and> \<zero> \<ls> \<one> \<ca> A \<longrightarrow> 
   \<one> \<ca> A \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S13 have S18: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<one> \<ca> A \<in> \<real>" .
   have S19: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S20: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S21: "(\<one> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> \<one> \<and> \<zero> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one> \<ca> A" by (rule MMI_addgtge0t)
   from S20 S21 have S22: "(\<one> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one> \<ca> A" by (rule MMI_mpanr1)
   from S19 S22 have S23: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one> \<ca> A" by (rule MMI_mpanl1)
   from S17 S18 S23 have S24: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   \<one> \<ca> A \<noteq> \<zero>" by (rule MMI_sylanc)
   from S9 S14 S16 S24 have S25: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   (A\<cdiv>(\<one> \<ca> A))\<cdot>(\<one> \<ca> A) = A" by (rule MMI_syl3anc)
   from S12 have S26: "A \<in> \<real> \<longrightarrow> \<one> \<ca> A \<in> \<real>" .
   from S26 have S27: "A \<in> \<real> \<longrightarrow> 
   \<one> \<ca> A \<in> \<complex>" by (rule MMI_recnd)
   have S28: "\<one> \<ca> A \<in> \<complex> \<longrightarrow> 
   \<one>\<cdot>(\<one> \<ca> A) = \<one> \<ca> A" by (rule MMI_mulid2t)
   from S27 S28 have S29: "A \<in> \<real> \<longrightarrow> 
   \<one>\<cdot>(\<one> \<ca> A) = \<one> \<ca> A" by (rule MMI_syl)
   from S29 have S30: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   \<one>\<cdot>(\<one> \<ca> A) = \<one> \<ca> A" by (rule MMI_adantr)
   from S8 S25 S30 have S31: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   (A\<cdiv>(\<one> \<ca> A))\<cdot>(\<one> \<ca> A) \<ls> \<one>\<cdot>(\<one> \<ca> A)" by (rule MMI_3brtr4d)
   have S32: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S33: "(A\<cdiv>(\<one> \<ca> A) \<in> \<real> \<and> \<one> \<in> \<real> \<and> \<one> \<ca> A \<in> \<real>) \<and> \<zero> \<ls> \<one> \<ca> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<ls> \<one> \<longleftrightarrow> 
   (A\<cdiv>(\<one> \<ca> A))\<cdot>(\<one> \<ca> A) \<ls> \<one>\<cdot>(\<one> \<ca> A)" by (rule MMI_ltmul1t)
   from S32 S33 have S34: "(A\<cdiv>(\<one> \<ca> A) \<in> \<real> \<and> \<one> \<ca> A \<in> \<real>) \<and> \<zero> \<ls> \<one> \<ca> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<ls> \<one> \<longleftrightarrow> 
   (A\<cdiv>(\<one> \<ca> A))\<cdot>(\<one> \<ca> A) \<ls> \<one>\<cdot>(\<one> \<ca> A)" by (rule MMI_mp3anl2)
   have S35: "A \<in> \<real> \<and> \<one> \<ca> A \<in> \<real> \<and> \<one> \<ca> A \<noteq> \<zero> \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<in> \<real>" by (rule MMI_redivclt)
   have S36: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S13 have S37: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<one> \<ca> A \<in> \<real>" .
   from S24 have S38: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   \<one> \<ca> A \<noteq> \<zero>" .
   from S35 S36 S37 S38 have S39: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<in> \<real>" by (rule MMI_syl3anc)
   from S13 have S40: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<one> \<ca> A \<in> \<real>" .
   from S39 S40 have S41: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<in> \<real> \<and> \<one> \<ca> A \<in> \<real>" by (rule MMI_jca)
   from S23 have S42: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one> \<ca> A" .
   from S34 S41 S42 have S43: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<ls> \<one> \<longleftrightarrow> 
   (A\<cdiv>(\<one> \<ca> A))\<cdot>(\<one> \<ca> A) \<ls> \<one>\<cdot>(\<one> \<ca> A)" by (rule MMI_sylanc)
   from S31 S43 show "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> A) \<ls> \<one>" by (rule MMI_mpbird)
qed

lemma (in MMIsar0) MMI_recrecltt: 
   shows "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> \<one> \<and> \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> A"
proof -
   have S1: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_recgt0t)
   have S2: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   have S3: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_rerecclt)
   from S2 S3 have S4: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_syldan)
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S6: "\<one>\<cdiv>A \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_ltaddpost)
   from S5 S6 have S7: "\<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_mpan2)
   from S4 S7 have S8: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_syl)
   from S1 S8 have S9: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_mpbid)
   have S10: "\<one> \<ca> \<one>\<cdiv>A \<in> \<real> \<and> \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> \<one>" by (rule MMI_recgt1t)
   from S4 have S11: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" .
   have S12: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S13: "\<one> \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<one> \<ca> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_axaddrcl)
   from S12 S13 have S14: "\<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<one> \<ca> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_mpan)
   from S11 S14 have S15: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ca> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_syl)
   from S9 have S16: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A" .
   have S17: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S15 have S18: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ca> \<one>\<cdiv>A \<in> \<real>" .
   have S19: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S20: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S21: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> \<one> \<ca> \<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longrightarrow> 
   \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_axlttrn)
   from S19 S20 S21 have S22: "\<one> \<ca> \<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longrightarrow> 
   \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_mp3an12)
   from S18 S22 have S23: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longrightarrow> 
   \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_syl)
   from S17 S23 have S24: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longrightarrow> 
   \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_mpani)
   from S16 S24 have S25: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_mpd)
   from S10 S15 S25 have S26: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> \<one>" by (rule MMI_sylanc)
   from S9 S26 have S27: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> \<one>" by (rule MMI_mpbid)
   have S28: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S4 have S29: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" .
   have S30: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S31: "\<one> \<in> \<real> \<and> \<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<longleftrightarrow> 
   \<one>\<cdiv>A \<ls> \<one>\<cdiv>A \<ca> \<one>" by (rule MMI_ltaddpost)
   from S30 S31 have S32: "\<one>\<cdiv>A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<longleftrightarrow> 
   \<one>\<cdiv>A \<ls> \<one>\<cdiv>A \<ca> \<one>" by (rule MMI_mpan)
   from S29 S32 have S33: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one> \<longleftrightarrow> 
   \<one>\<cdiv>A \<ls> \<one>\<cdiv>A \<ca> \<one>" by (rule MMI_syl)
   from S28 S33 have S34: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>A \<ls> \<one>\<cdiv>A \<ca> \<one>" by (rule MMI_mpbii)
   from S4 have S35: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<one>\<cdiv>A \<in> \<real>" .
   from S35 have S36: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>A \<in> \<complex>" by (rule MMI_recnd)
   have S37: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S38: "\<one>\<cdiv>A \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
   \<one>\<cdiv>A \<ca> \<one> = \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_axaddcom)
   from S37 S38 have S39: "\<one>\<cdiv>A \<in> \<complex> \<longrightarrow> 
   \<one>\<cdiv>A \<ca> \<one> = \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_mpan2)
   from S36 S39 have S40: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>A \<ca> \<one> = \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_syl)
   from S34 S40 have S41: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>A \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_breqtrd)
   have S42: "(A \<in> \<real> \<and> \<one> \<ca> \<one>\<cdiv>A \<in> \<real>) \<and> \<zero> \<ls> A \<and> \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A \<longrightarrow> 
   \<one>\<cdiv>A \<ls> \<one> \<ca> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> A" by (rule MMI_ltrec1t)
   have S43: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S15 have S44: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one> \<ca> \<one>\<cdiv>A \<in> \<real>" .
   from S43 S44 have S45: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   A \<in> \<real> \<and> \<one> \<ca> \<one>\<cdiv>A \<in> \<real>" by (rule MMI_jca)
   have S46: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_pm3_27)
   from S25 have S47: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" .
   from S46 S47 have S48: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<zero> \<ls> A \<and> \<zero> \<ls> \<one> \<ca> \<one>\<cdiv>A" by (rule MMI_jca)
   from S42 S45 S48 have S49: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>A \<ls> \<one> \<ca> \<one>\<cdiv>A \<longleftrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> A" by (rule MMI_sylanc)
   from S41 S49 have S50: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> A" by (rule MMI_mpbid)
   from S27 S50 show "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> 
   \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> \<one> \<and> \<one>\<cdiv>(\<one> \<ca> \<one>\<cdiv>A) \<ls> A" by (rule MMI_jca)
qed

lemma (in MMIsar0) MMI_le2msqt: 
   shows "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   from S1 have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B" by (rule MMI_anbi1d)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B" by (rule MMI_breq1)
   have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<and> A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_opreq12)
   from S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A = ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_anidms)
   from S5 have S6: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdot>A \<lsq> B\<cdot>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> B\<cdot>B" by (rule MMI_breq1d)
   from S3 S6 have S7: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> B\<cdot>B" by (rule MMI_bibi12d)
   from S2 S7 have S8: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B) \<longleftrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> B\<cdot>B)" by (rule MMI_imbi12d)
   have S9: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   from S9 have S10: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B \<longleftrightarrow> 
   \<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anbi2d)
   have S11: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2)
   have S12: "B =  if(B \<in> \<real>, B, \<zero>) \<and> B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<cdot>B = ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_opreq12)
   from S12 have S13: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   B\<cdot>B = ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_anidms)
   from S13 have S14: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> B\<cdot>B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_breq2d)
   from S11 S14 have S15: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> B\<cdot>B) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_bibi12d)
   from S10 S15 have S16: "B =  if(B \<in> \<real>, B, \<zero>) \<longrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> B \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> B \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> B\<cdot>B) \<longleftrightarrow> 
   (\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>)))" by (rule MMI_imbi12d)
   have S17: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S17 have S18: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   have S19: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S19 have S20: " if(B \<in> \<real>, B, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S18 S20 have S21: "\<zero> \<lsq> ( if(A \<in> \<real>, A, \<zero>)) \<and> \<zero> \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdot>( if(A \<in> \<real>, A, \<zero>)) \<lsq> ( if(B \<in> \<real>, B, \<zero>))\<cdot>( if(B \<in> \<real>, B, \<zero>))" by (rule MMI_le2msq)
   from S8 S16 S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B" by (rule MMI_dedth2h)
   from S22 have S23: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B" by (rule MMI_imp)
   from S23 show "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A\<cdot>A \<lsq> B\<cdot>B" by (rule MMI_an4s)
qed

lemma (in MMIsar0) MMI_halfpos: assumes A1: "A \<in> \<real>"   
   shows "\<zero> \<ls> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A1 have S2: "A \<in> \<real>".
   from A1 have S3: "A \<in> \<real>".
   from S1 S2 S3 have S4: "\<zero> \<ls> A \<longleftrightarrow> 
   \<zero> \<ca> A \<ls> A \<ca> A" by (rule MMI_ltadd1)
   from A1 have S5: "A \<in> \<real>".
   from S5 have S6: "A \<in> \<complex>" by (rule MMI_recn)
   from S6 have S7: "\<zero> \<ca> A = A" by (rule MMI_addid2)
   from S6 have S8: "A \<in> \<complex>" .
   from S8 have S9: "(\<one> \<ca> \<one>)\<cdot>A = A \<ca> A" by (rule MMI_1p1times)
   from S9 have S10: "A \<ca> A = (\<one> \<ca> \<one>)\<cdot>A" by (rule MMI_eqcomi)
   from S7 S10 have S11: "\<zero> \<ca> A \<ls> A \<ca> A \<longleftrightarrow> 
   A \<ls> (\<one> \<ca> \<one>)\<cdot>A" by (rule MMI_breq12i)
   from A1 have S12: "A \<in> \<real>".
   have S13: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S14: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S13 S14 have S15: "\<one> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from A1 have S16: "A \<in> \<real>".
   from S15 S16 have S17: "(\<one> \<ca> \<one>)\<cdot>A \<in> \<real>" by (rule MMI_remulcl)
   from S15 have S18: "\<one> \<ca> \<one> \<in> \<real>" .
   have S19: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S20: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S21: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S22: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S19 S20 S21 S22 have S23: "\<zero> \<ls> \<one> \<ca> \<one>" by (rule MMI_addgt0i)
   from S12 S17 S18 S23 have S24: "A \<ls> (\<one> \<ca> \<one>)\<cdot>A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> (\<one> \<ca> \<one>)\<cdot>A\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_ltdiv1i)
   from S11 S24 have S25: "\<zero> \<ca> A \<ls> A \<ca> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> (\<one> \<ca> \<one>)\<cdot>A\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_bitr)
   have S26: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S27: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S26 S27 have S28: "\<one> \<ca> \<one> \<in> \<complex>" by (rule MMI_addcl)
   from S6 have S29: "A \<in> \<complex>" .
   from S15 have S30: "\<one> \<ca> \<one> \<in> \<real>" .
   from S23 have S31: "\<zero> \<ls> \<one> \<ca> \<one>" .
   from S30 S31 have S32: "\<one> \<ca> \<one> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S28 S29 S32 have S33: "(\<one> \<ca> \<one>)\<cdot>A\<cdiv>(\<one> \<ca> \<one>) = A" by (rule MMI_divcan3)
   from S33 have S34: "A\<cdiv>(\<one> \<ca> \<one>) \<ls> (\<one> \<ca> \<one>)\<cdot>A\<cdiv>(\<one> \<ca> \<one>) \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_breq2i)
   from S4 S25 S34 show "\<zero> \<ls> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_3bitr)
qed

(********* 481-489*******************************)


lemma (in MMIsar0) MMI_ledivp1t: 
   shows "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   (A\<cdiv>(B \<ca> \<one>))\<cdot>B \<lsq> A"
proof -
   have S1: "(B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<and> A\<cdiv>(B \<ca> \<one>) \<in> \<real>) \<and> \<zero> \<lsq> A\<cdiv>(B \<ca> \<one>) \<and> B \<lsq> B \<ca> \<one> \<longrightarrow> 
   (A\<cdiv>(B \<ca> \<one>))\<cdot>B \<lsq> (A\<cdiv>(B \<ca> \<one>))\<cdot>(B \<ca> \<one>)" by (rule MMI_lemul2it)
   have S2: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_26)
   from S2 have S3: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<in> \<real>" by (rule MMI_adantl)
   have S4: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
   from S4 have S5: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<ca> \<one> \<in> \<real>" by (rule MMI_ad2antrl)
   have S6: "A \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<and> B \<ca> \<one> \<noteq> \<zero> \<longrightarrow> 
   A\<cdiv>(B \<ca> \<one>) \<in> \<real>" by (rule MMI_redivclt)
   have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S4 have S8: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   from S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<ca> \<one> \<in> \<real>" by (rule MMI_ad2antrl)
   have S10: "B \<ca> \<one> \<in> \<real> \<and> \<zero> \<ls> B \<ca> \<one> \<longrightarrow> 
   B \<ca> \<one> \<noteq> \<zero>" by (rule MMI_gt0ne0t)
   from S4 have S11: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   from S11 have S12: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<ca> \<one> \<in> \<real>" by (rule MMI_adantr)
   have S13: "B \<in> \<real> \<longrightarrow> B \<ls> B \<ca> \<one>" by (rule MMI_ltp1t)
   from S4 have S14: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   have S15: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S16: "\<zero> \<in> \<real> \<and> B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<and> B \<ls> B \<ca> \<one> \<longrightarrow> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_lelttrt)
   from S15 S16 have S17: "B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<and> B \<ls> B \<ca> \<one> \<longrightarrow> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_mp3an1)
   from S14 S17 have S18: "B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<and> B \<ls> B \<ca> \<one> \<longrightarrow> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_mpdan)
   from S13 S18 have S19: "B \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> B \<longrightarrow> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_mpan2d)
   from S19 have S20: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_imp)
   from S10 S12 S20 have S21: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ca> \<one> \<noteq> \<zero>" by (rule MMI_sylanc)
   from S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ca> \<one> \<noteq> \<zero>" by (rule MMI_adantl)
   from S6 S7 S9 S22 have S23: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A\<cdiv>(B \<ca> \<one>) \<in> \<real>" by (rule MMI_syl3anc)
   from S23 have S24: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A\<cdiv>(B \<ca> \<one>) \<in> \<real>" by (rule MMI_adantlr)
   from S3 S5 S24 have S25: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<and> A\<cdiv>(B \<ca> \<one>) \<in> \<real>" by (rule MMI_3jca)
   have S26: "(A \<in> \<real> \<and> B \<ca> \<one> \<in> \<real>) \<and> \<zero> \<lsq> A \<and> \<zero> \<ls> B \<ca> \<one> \<longrightarrow> 
   \<zero> \<lsq> A\<cdiv>(B \<ca> \<one>)" by (rule MMI_divge0t)
   have S27: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   from S12 have S28: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   from S27 S28 have S29: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   A \<in> \<real> \<and> B \<ca> \<one> \<in> \<real>" by (rule MMI_anim12i)
   have S30: "A \<in> \<real> \<and> \<zero> \<lsq> A \<longrightarrow> \<zero> \<lsq> A" by (rule MMI_pm3_27)
   from S20 have S31: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> \<zero> \<ls> B \<ca> \<one>" .
   from S30 S31 have S32: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   \<zero> \<lsq> A \<and> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_anim12i)
   from S26 S29 S32 have S33: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   \<zero> \<lsq> A\<cdiv>(B \<ca> \<one>)" by (rule MMI_sylanc)
   from S13 have S34: "B \<in> \<real> \<longrightarrow> B \<ls> B \<ca> \<one>" .
   from S34 have S35: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<ls> B \<ca> \<one>" by (rule MMI_adantr)
   from S4 have S36: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   have S37: "B \<in> \<real> \<and> B \<ca> \<one> \<in> \<real> \<longrightarrow> 
   B \<ls> B \<ca> \<one> \<longrightarrow> B \<lsq> B \<ca> \<one>" by (rule MMI_ltlet)
   from S36 S37 have S38: "B \<in> \<real> \<longrightarrow> 
   B \<ls> B \<ca> \<one> \<longrightarrow> B \<lsq> B \<ca> \<one>" by (rule MMI_mpdan)
   from S38 have S39: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ls> B \<ca> \<one> \<longrightarrow> B \<lsq> B \<ca> \<one>" by (rule MMI_adantr)
   from S35 S39 have S40: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<lsq> B \<ca> \<one>" by (rule MMI_mpd)
   from S40 have S41: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> B \<lsq> B \<ca> \<one>" by (rule MMI_adantl)
   from S33 S41 have S42: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   \<zero> \<lsq> A\<cdiv>(B \<ca> \<one>) \<and> B \<lsq> B \<ca> \<one>" by (rule MMI_jca)
   from S1 S25 S42 have S43: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   (A\<cdiv>(B \<ca> \<one>))\<cdot>B \<lsq> (A\<cdiv>(B \<ca> \<one>))\<cdot>(B \<ca> \<one>)" by (rule MMI_sylanc)
   have S44: "B \<ca> \<one> \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<ca> \<one> \<noteq> \<zero> \<longrightarrow> 
   (A\<cdiv>(B \<ca> \<one>))\<cdot>(B \<ca> \<one>) = A" by (rule MMI_divcan1t)
   from S4 have S45: "B \<in> \<real> \<longrightarrow> B \<ca> \<one> \<in> \<real>" .
   from S45 have S46: "B \<in> \<real> \<longrightarrow> 
   B \<ca> \<one> \<in> \<complex>" by (rule MMI_recnd)
   from S46 have S47: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ca> \<one> \<in> \<complex>" by (rule MMI_ad2antrl)
   have S48: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S48 have S49: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> A \<in> \<complex>" by (rule MMI_ad2antrr)
   from S21 have S50: "B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ca> \<one> \<noteq> \<zero>" .
   from S50 have S51: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   B \<ca> \<one> \<noteq> \<zero>" by (rule MMI_adantl)
   from S44 S47 S49 S51 have S52: "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   (A\<cdiv>(B \<ca> \<one>))\<cdot>(B \<ca> \<one>) = A" by (rule MMI_syl3anc)
   from S43 S52 show "(A \<in> \<real> \<and> \<zero> \<lsq> A) \<and> B \<in> \<real> \<and> \<zero> \<lsq> B \<longrightarrow> 
   (A\<cdiv>(B \<ca> \<one>))\<cdot>B \<lsq> A" by auto (*(rule MMI_breqtrd)*)
qed

lemma (in MMIsar0) MMI_ledivp1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> A\<cdot>C \<lsq> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A3 have S2: "C \<in> \<real>".
   from S1 S2 have S3: "A\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from A1 have S4: "A \<in> \<real>".
   from A3 have S5: "C \<in> \<real>".
   have S6: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S5 S6 have S7: "C \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S4 S7 have S8: "A\<cdot>(C \<ca> \<one>) \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S9: "B \<in> \<real>".
   from S3 S8 S9 have S10: "A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>) \<and> A\<cdot>(C \<ca> \<one>) \<lsq> B \<longrightarrow> A\<cdot>C \<lsq> B" by (rule MMI_letr)
   from A3 have S11: "C \<in> \<real>".
   from S7 have S12: "C \<ca> \<one> \<in> \<real>" .
   from A3 have S13: "C \<in> \<real>".
   from S13 have S14: "C \<ls> C \<ca> \<one>" by (rule MMI_ltp1)
   from S11 S12 S14 have S15: "C \<lsq> C \<ca> \<one>" by (rule MMI_ltlei)
   from A3 have S16: "C \<in> \<real>".
   from S7 have S17: "C \<ca> \<one> \<in> \<real>" .
   from A1 have S18: "A \<in> \<real>".
   have S19: "(C \<in> \<real> \<and> C \<ca> \<one> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> A \<and> C \<lsq> C \<ca> \<one> \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_lemul2it)
   from S19 have S20: "C \<in> \<real> \<and> C \<ca> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> C \<lsq> C \<ca> \<one> \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_ex)
   from S16 S17 S18 S20 have S21: "\<zero> \<lsq> A \<and> C \<lsq> C \<ca> \<one> \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_mp3an)
   from S15 S21 have S22: "\<zero> \<lsq> A \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_mpan2)
   from S22 have S23: "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_3ad2ant1)
   from S14 have S24: "C \<ls> C \<ca> \<one>" .
   have S25: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A3 have S26: "C \<in> \<real>".
   from S7 have S27: "C \<ca> \<one> \<in> \<real>" .
   from S25 S26 S27 have S28: "\<zero> \<lsq> C \<and> C \<ls> C \<ca> \<one> \<longrightarrow> \<zero> \<ls> C \<ca> \<one>" by (rule MMI_lelttr)
   from S24 S28 have S29: "\<zero> \<lsq> C \<longrightarrow> \<zero> \<ls> C \<ca> \<one>" by (rule MMI_mpan2)
   from S7 have S30: "C \<ca> \<one> \<in> \<real>" .
   from S30 have S31: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   C \<ca> \<one> \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from A2 have S32: "B \<in> \<real>".
   from S7 have S33: "C \<ca> \<one> \<in> \<real>" .
   from S32 S33 have S34: "C \<ca> \<one> \<noteq> \<zero> \<longrightarrow> 
   B\<cdiv>(C \<ca> \<one>) \<in> \<real>" by (rule MMI_redivclz)
   from S31 S34 have S35: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   B\<cdiv>(C \<ca> \<one>) \<in> \<real>" by (rule MMI_syl)
   from S7 have S36: "C \<ca> \<one> \<in> \<real>" .
   from A1 have S37: "A \<in> \<real>".
   have S38: "(A \<in> \<real> \<and> B\<cdiv>(C \<ca> \<one>) \<in> \<real> \<and> C \<ca> \<one> \<in> \<real>) \<and> \<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_lemul1t)
   from S37 S38 have S39: "(B\<cdiv>(C \<ca> \<one>) \<in> \<real> \<and> C \<ca> \<one> \<in> \<real>) \<and> \<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_mp3anl1)
   from S36 S39 have S40: "B\<cdiv>(C \<ca> \<one>) \<in> \<real> \<and> \<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_mpanl2)
   from S35 S40 have S41: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_mpancom)
   from S41 have S42: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_biimpd)
   from S29 S42 have S43: "\<zero> \<lsq> C \<longrightarrow> 
   A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_syl)
   from S43 have S44: "\<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_imp)
   from S29 have S45: "\<zero> \<lsq> C \<longrightarrow> \<zero> \<ls> C \<ca> \<one>" .
   from S31 have S46: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   C \<ca> \<one> \<noteq> \<zero>" .
   from S7 have S47: "C \<ca> \<one> \<in> \<real>" .
   from S47 have S48: "C \<ca> \<one> \<in> \<complex>" by (rule MMI_recn)
   from A2 have S49: "B \<in> \<real>".
   from S49 have S50: "B \<in> \<complex>" by (rule MMI_recn)
   from S48 S50 have S51: "C \<ca> \<one> \<noteq> \<zero> \<longrightarrow> 
   (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>) = B" by (rule MMI_divcan1z)
   from S45 S46 S51 have S52: "\<zero> \<lsq> C \<longrightarrow> 
   (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>) = B" by (rule MMI_3syl)
   from S52 have S53: "\<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>) = B" by (rule MMI_adantr)
   from S44 S53 have S54: "\<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> B" by auto (*(rule MMI_breqtrd)*)
   from S54 have S55: "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<lsq> B" by (rule MMI_3adant1)
   from S10 S23 S55 show "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<lsq> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> A\<cdot>C \<lsq> B" by (rule MMI_sylanc)
qed

lemma (in MMIsar0) MMI_ltdivp1: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>"   
   shows "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> A\<cdot>C \<ls> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A3 have S2: "C \<in> \<real>".
   from S1 S2 have S3: "A\<cdot>C \<in> \<real>" by (rule MMI_remulcl)
   from A1 have S4: "A \<in> \<real>".
   from A3 have S5: "C \<in> \<real>".
   have S6: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S5 S6 have S7: "C \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S4 S7 have S8: "A\<cdot>(C \<ca> \<one>) \<in> \<real>" by (rule MMI_remulcl)
   from A2 have S9: "B \<in> \<real>".
   from S3 S8 S9 have S10: "A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>) \<and> A\<cdot>(C \<ca> \<one>) \<ls> B \<longrightarrow> A\<cdot>C \<ls> B" by (rule MMI_lelttr)
   from A3 have S11: "C \<in> \<real>".
   from S7 have S12: "C \<ca> \<one> \<in> \<real>" .
   from A3 have S13: "C \<in> \<real>".
   from S13 have S14: "C \<ls> C \<ca> \<one>" by (rule MMI_ltp1)
   from S11 S12 S14 have S15: "C \<lsq> C \<ca> \<one>" by (rule MMI_ltlei)
   from A3 have S16: "C \<in> \<real>".
   from S7 have S17: "C \<ca> \<one> \<in> \<real>" .
   from A1 have S18: "A \<in> \<real>".
   have S19: "(C \<in> \<real> \<and> C \<ca> \<one> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<lsq> A \<and> C \<lsq> C \<ca> \<one> \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_lemul2it)
   from S19 have S20: "C \<in> \<real> \<and> C \<ca> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<and> C \<lsq> C \<ca> \<one> \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_ex)
   from S16 S17 S18 S20 have S21: "\<zero> \<lsq> A \<and> C \<lsq> C \<ca> \<one> \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_mp3an)
   from S15 S21 have S22: "\<zero> \<lsq> A \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_mpan2)
   from S22 have S23: "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>C \<lsq> A\<cdot>(C \<ca> \<one>)" by (rule MMI_3ad2ant1)
   from S14 have S24: "C \<ls> C \<ca> \<one>" .
   have S25: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from A3 have S26: "C \<in> \<real>".
   from S7 have S27: "C \<ca> \<one> \<in> \<real>" .
   from S25 S26 S27 have S28: "\<zero> \<lsq> C \<and> C \<ls> C \<ca> \<one> \<longrightarrow> \<zero> \<ls> C \<ca> \<one>" by (rule MMI_lelttr)
   from S24 S28 have S29: "\<zero> \<lsq> C \<longrightarrow> \<zero> \<ls> C \<ca> \<one>" by (rule MMI_mpan2)
   from S7 have S30: "C \<ca> \<one> \<in> \<real>" .
   from S30 have S31: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   C \<ca> \<one> \<noteq> \<zero>" by (rule MMI_gt0ne0)
   from A2 have S32: "B \<in> \<real>".
   from S7 have S33: "C \<ca> \<one> \<in> \<real>" .
   from S32 S33 have S34: "C \<ca> \<one> \<noteq> \<zero> \<longrightarrow> 
   B\<cdiv>(C \<ca> \<one>) \<in> \<real>" by (rule MMI_redivclz)
   from S31 S34 have S35: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   B\<cdiv>(C \<ca> \<one>) \<in> \<real>" by (rule MMI_syl)
   from S7 have S36: "C \<ca> \<one> \<in> \<real>" .
   from A1 have S37: "A \<in> \<real>".
   have S38: "(A \<in> \<real> \<and> B\<cdiv>(C \<ca> \<one>) \<in> \<real> \<and> C \<ca> \<one> \<in> \<real>) \<and> \<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<ls> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_ltmul1t)
   from S37 S38 have S39: "(B\<cdiv>(C \<ca> \<one>) \<in> \<real> \<and> C \<ca> \<one> \<in> \<real>) \<and> \<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<ls> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_mp3anl1)
   from S36 S39 have S40: "B\<cdiv>(C \<ca> \<one>) \<in> \<real> \<and> \<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<ls> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_mpanl2)
   from S35 S40 have S41: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<ls> B\<cdiv>(C \<ca> \<one>) \<longleftrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_mpancom)
   from S41 have S42: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_biimpd)
   from S29 S42 have S43: "\<zero> \<lsq> C \<longrightarrow> 
   A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_syl)
   from S43 have S44: "\<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>)" by (rule MMI_imp)
   from S29 have S45: "\<zero> \<lsq> C \<longrightarrow> \<zero> \<ls> C \<ca> \<one>" .
   from S31 have S46: "\<zero> \<ls> C \<ca> \<one> \<longrightarrow> 
   C \<ca> \<one> \<noteq> \<zero>" .
   from S7 have S47: "C \<ca> \<one> \<in> \<real>" .
   from S47 have S48: "C \<ca> \<one> \<in> \<complex>" by (rule MMI_recn)
   from A2 have S49: "B \<in> \<real>".
   from S49 have S50: "B \<in> \<complex>" by (rule MMI_recn)
   from S48 S50 have S51: "C \<ca> \<one> \<noteq> \<zero> \<longrightarrow> 
   (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>) = B" by (rule MMI_divcan1z)
   from S45 S46 S51 have S52: "\<zero> \<lsq> C \<longrightarrow> 
   (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>) = B" by (rule MMI_3syl)
   from S52 have S53: "\<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   (B\<cdiv>(C \<ca> \<one>))\<cdot>(C \<ca> \<one>) = B" by (rule MMI_adantr)
   from S44 S53 have S54: "\<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> B" by (rule MMI_breqtrd)
   from S54 have S55: "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> 
   A\<cdot>(C \<ca> \<one>) \<ls> B" by (rule MMI_3adant1)
   from S10 S23 S55 show "\<zero> \<lsq> A \<and> \<zero> \<lsq> C \<and> A \<ls> B\<cdiv>(C \<ca> \<one>) \<longrightarrow> A\<cdot>C \<ls> B" by (rule MMI_sylanc)
qed

lemma (in MMIsar0) MMI_posex: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "\<zero> \<ls> A" and
    A4: "\<zero> \<ls> B"   
   shows " \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   from S1 S2 have S3: "\<not>(A = B) \<longleftrightarrow> A \<ls> B \<or> B \<ls> A" by (rule MMI_lttri2)
   from S3 have S4: "\<not>(A = B) \<longrightarrow> A \<ls> B \<or> B \<ls> A" by (rule MMI_biimp)
   from S4 have S5: "A = B \<or> A \<ls> B \<or> B \<ls> A" by (rule MMI_orri)
   have S6: "A = B \<or> A \<ls> B \<or> B \<ls> A \<longleftrightarrow> 
   A \<ls> B \<or> A = B \<or> B \<ls> A" by (rule MMI_or12)
   from S5 S6 have S7: "A \<ls> B \<or> A = B \<or> B \<ls> A" by (rule MMI_mpbi)
   from A3 have S8: "\<zero> \<ls> A".
   from A1 have S9: "A \<in> \<real>".
   from S9 have S10: "\<zero> \<ls> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_halfpos)
   from S8 S10 have S11: "A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_mpbi)
   from A1 have S12: "A \<in> \<real>".
   have S13: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S14: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S13 S14 have S15: "\<one> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S15 have S16: "\<one> \<ca> \<one> \<in> \<real>" .
   have S17: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S18: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S19: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S20: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S17 S18 S19 S20 have S21: "\<zero> \<ls> \<one> \<ca> \<one>" by (rule MMI_addgt0i)
   from S16 S21 have S22: "\<one> \<ca> \<one> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S12 S15 S22 have S23: "A\<cdiv>(\<one> \<ca> \<one>) \<in> \<real>" by (rule MMI_redivcl)
   from A1 have S24: "A \<in> \<real>".
   from A2 have S25: "B \<in> \<real>".
   from S23 S24 S25 have S26: "A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A \<ls> B \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_lttr)
   from S11 S26 have S27: "A \<ls> B \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_mpan)
   from S11 have S28: "A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" .
   from S27 S28 have S29: "A \<ls> B \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_jctil)
   from A1 have S30: "A \<in> \<real>".
   from S15 have S31: "\<one> \<ca> \<one> \<in> \<real>" .
   from A3 have S32: "\<zero> \<ls> A".
   from S21 have S33: "\<zero> \<ls> \<one> \<ca> \<one>" .
   from S30 S31 S32 S33 have S34: "\<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_divgt0i)
   from S29 S34 have S35: "A \<ls> B \<longrightarrow> 
   \<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>) \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_jctil)
   from S23 have S36: "A\<cdiv>(\<one> \<ca> \<one>) \<in> \<real>" .
   from S35 S36 have S37: "A \<ls> B \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<in> \<real> \<and> \<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>) \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" 
     by (rule MMI_jctil)
   { fix x
     have S38: "x = A\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       \<zero> \<ls> x \<longleftrightarrow> 
       \<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_breq2)
     have S39: "x = A\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       x \<ls> A \<longleftrightarrow> 
       A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_breq1)
     have S40: "x = A\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       x \<ls> B \<longleftrightarrow> 
       A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_breq1)
     from S39 S40 have S41: "x = A\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       x \<ls> A \<and> x \<ls> B \<longleftrightarrow> 
       A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_anbi12d)
     from S38 S41 have  "x = A\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B \<longleftrightarrow> 
       \<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>) \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_anbi12d)
   } then have S42: "\<forall>x.  x = A\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B \<longleftrightarrow> 
       \<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>) \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by simp
   from S42 have S43: 
     "A\<cdiv>(\<one> \<ca> \<one>) \<in> \<real> \<and> \<zero> \<ls> A\<cdiv>(\<one> \<ca> \<one>) \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> A\<cdiv>(\<one> \<ca> \<one>) \<ls> B \<longrightarrow>
     ( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B)" by (rule MMI_rcla4ev)
   from S37 S43 have S44: "A \<ls> B \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B)" by (rule MMI_syl)
   from A4 have S45: "\<zero> \<ls> B".
   from A2 have S46: "B \<in> \<real>".
   from S46 have S47: "\<zero> \<ls> B \<longleftrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_halfpos)
   from S45 S47 have S48: "B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_mpbi)
   have S49: "A = B \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<longleftrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_breq2)
   from S48 S49 have S50: "A = B \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_mpbiri)
   from S48 have S51: "B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" .
   from A2 have S52: "B \<in> \<real>".
   from S15 have S53: "\<one> \<ca> \<one> \<in> \<real>" .
   from S22 have S54: "\<one> \<ca> \<one> \<noteq> \<zero>" .
   from S52 S53 S54 have S55: "B\<cdiv>(\<one> \<ca> \<one>) \<in> \<real>" by (rule MMI_redivcl)
   from A2 have S56: "B \<in> \<real>".
   from A1 have S57: "A \<in> \<real>".
   from S55 S56 S57 have S58: "B\<cdiv>(\<one> \<ca> \<one>) \<ls> B \<and> B \<ls> A \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_lttr)
   from S51 S58 have S59: "B \<ls> A \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_mpan)
   from S50 S59 have S60: "A = B \<or> B \<ls> A \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_jaoi)
   from S48 have S61: "B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" .
   from S60 S61 have S62: "A = B \<or> B \<ls> A \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_jctir)
   from A2 have S63: "B \<in> \<real>".
   from S15 have S64: "\<one> \<ca> \<one> \<in> \<real>" .
   from A4 have S65: "\<zero> \<ls> B".
   from S21 have S66: "\<zero> \<ls> \<one> \<ca> \<one>" .
   from S63 S64 S65 S66 have S67: "\<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_divgt0i)
   from S62 S67 have S68: "A = B \<or> B \<ls> A \<longrightarrow> 
   \<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>) \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_jctil)
   from S55 have S69: "B\<cdiv>(\<one> \<ca> \<one>) \<in> \<real>" .
   from S68 S69 have S70: "A = B \<or> B \<ls> A \<longrightarrow> 
   B\<cdiv>(\<one> \<ca> \<one>) \<in> \<real> \<and> \<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>) \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_jctil)
   { fix x
     have S71: "x = B\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       \<zero> \<ls> x \<longleftrightarrow> 
       \<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_breq2)
     have S72: "x = B\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       x \<ls> A \<longleftrightarrow> 
       B\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_breq1)
     have S73: "x = B\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       x \<ls> B \<longleftrightarrow> 
       B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_breq1)
     from S72 S73 have S74: "x = B\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       x \<ls> A \<and> x \<ls> B \<longleftrightarrow> 
       B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_anbi12d)
     from S71 S74 have  "x = B\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B \<longleftrightarrow> 
       \<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>) \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by (rule MMI_anbi12d)
   } then have S75: "\<forall> x. x = B\<cdiv>(\<one> \<ca> \<one>) \<longrightarrow> 
       \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B \<longleftrightarrow> 
       \<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>) \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B" by simp
     from S75 have S76: "B\<cdiv>(\<one> \<ca> \<one>) \<in> \<real> \<and> \<zero> \<ls> B\<cdiv>(\<one> \<ca> \<one>) \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<and> B\<cdiv>(\<one> \<ca> \<one>) \<ls> B \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B)" by (rule MMI_rcla4ev)
   from S70 S76 have S77: "A = B \<or> B \<ls> A \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B)" by (rule MMI_syl)
   from S44 S77 have S78: "A \<ls> B \<or> A = B \<or> B \<ls> A \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B)" by (rule MMI_jaoi)
   from S7 S78 show " \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> x \<ls> A \<and> x \<ls> B" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_max1: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))"
proof -
   have S1: "\<not>(A \<lsq> B) \<longrightarrow>  if(A \<lsq> B, B, A) = A" by (rule MMI_iffalse)
   from S1 have S2: "\<not>(A \<lsq> B) \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A)) \<longleftrightarrow> A \<lsq> A" by (rule MMI_breq2d)
   have S3: "A \<in> \<real> \<longrightarrow> A \<lsq> A" by (rule MMI_leidt)
   from S2 S3 have S4: "\<not>(A \<lsq> B) \<longrightarrow> 
   A \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_syl5bir)
   from S4 have S5: "A \<in> \<real> \<longrightarrow> 
   \<not>(A \<lsq> B) \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_com12)
   have S6: "A \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_id)
   have S7: "A \<lsq> B \<longrightarrow>  if(A \<lsq> B, B, A) = B" by (rule MMI_iftrue)
   from S6 S7 have S8: "A \<lsq> B \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by auto (*by (rule MMI_breqtrrd)*)
   from S5 S8 have S9: "A \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_pm2_61d2)
   from S9 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_adantr)
qed

lemma (in MMIsar0) MMI_max1ALT: 
   shows "A \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))"
proof -
   have S1: "\<not>(A \<lsq> B) \<longrightarrow>  if(A \<lsq> B, B, A) = A" by (rule MMI_iffalse)
   from S1 have S2: "\<not>(A \<lsq> B) \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A)) \<longleftrightarrow> A \<lsq> A" by (rule MMI_breq2d)
   have S3: "A \<in> \<real> \<longrightarrow> A \<lsq> A" by (rule MMI_leidt)
   from S2 S3 have S4: "\<not>(A \<lsq> B) \<longrightarrow> 
   A \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_syl5bir)
   from S4 have S5: "A \<in> \<real> \<longrightarrow> 
   \<not>(A \<lsq> B) \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_com12)
   have S6: "A \<lsq> B \<longrightarrow> A \<lsq> B" by (rule MMI_id)
   have S7: "A \<lsq> B \<longrightarrow>  if(A \<lsq> B, B, A) = B" by (rule MMI_iftrue)
   from S6 S7 have S8: "A \<lsq> B \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by simp (*by (rule MMI_breqtrrd)*)
   from S5 S8 show "A \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_pm2_61d2)
qed

lemma (in MMIsar0) MMI_max2: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A))"
proof -
   have S1: "B \<in> \<real> \<longrightarrow> B \<lsq> B" by (rule MMI_leidt)
   from S1 have S2: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> A \<lsq> B \<longrightarrow> B \<lsq> B" by (rule MMI_ad2antlr)
   have S3: "A \<lsq> B \<longrightarrow>  if(A \<lsq> B, B, A) = B" by (rule MMI_iftrue)
   from S3 have S4: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> A \<lsq> B \<longrightarrow>  if(A \<lsq> B, B, A) = B" by (rule MMI_adantl)
   from S2 S4 have S5: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> A \<lsq> B \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A))" by simp(*by (rule MMI_breqtrrd)*)
   have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<lsq> B \<or> B \<lsq> A" by (rule MMI_letrit)
   from S6 have S7: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<not>(A \<lsq> B) \<longrightarrow> B \<lsq> A" by (rule MMI_orcanai)
   have S8: "\<not>(A \<lsq> B) \<longrightarrow>  if(A \<lsq> B, B, A) = A" by (rule MMI_iffalse)
   from S8 have S9: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<not>(A \<lsq> B) \<longrightarrow>  if(A \<lsq> B, B, A) = A" by (rule MMI_adantl)
   from S7 S9 have S10: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<not>(A \<lsq> B) \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A))" by simp (*by (rule MMI_breqtrrd)*)
   from S5 S10 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_pm2_61dan)
qed

lemma (in MMIsar0) MMI_maxlet: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longleftrightarrow> A \<lsq> C \<and> B \<lsq> C"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_max1)
   from S1 have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_3adant3)
   have S3: "A \<in> \<real> \<and>  if(A \<lsq> B, B, A) \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A)) \<and> ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> A \<lsq> C" by (rule MMI_letrt)
   have S4: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_3simp1)
   have S5: "B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
    if(A \<lsq> B, B, A) \<in> \<real>" by (rule MMI_ifcl)
   from S5 have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
    if(A \<lsq> B, B, A) \<in> \<real>" by (rule MMI_ancoms)
   from S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
    if(A \<lsq> B, B, A) \<in> \<real>" by (rule MMI_3adant3)
   have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" by (rule MMI_3simp3)
   from S3 S4 S7 S8 have S9: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<lsq> ( if(A \<lsq> B, B, A)) \<and> ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> A \<lsq> C" by (rule MMI_syl3anc)
   from S2 S9 have S10: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> A \<lsq> C" by (rule MMI_mpand)
   have S11: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_max2)
   from S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A))" by (rule MMI_3adant3)
   have S13: "B \<in> \<real> \<and>  if(A \<lsq> B, B, A) \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A)) \<and> ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> B \<lsq> C" by (rule MMI_letrt)
   have S14: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_3simp2)
   from S7 have S15: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
    if(A \<lsq> B, B, A) \<in> \<real>" .
   from S8 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> C \<in> \<real>" .
   from S13 S14 S15 S16 have S17: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   B \<lsq> ( if(A \<lsq> B, B, A)) \<and> ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> B \<lsq> C" by (rule MMI_syl3anc)
   from S12 S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> B \<lsq> C" by (rule MMI_mpand)
   from S10 S18 have S19: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longrightarrow> A \<lsq> C \<and> B \<lsq> C" by (rule MMI_jcad)
   have S20: "A \<lsq> B \<longrightarrow>  if(A \<lsq> B, B, A) = B" by (rule MMI_iftrue)
   from S20 have S21: "A \<lsq> B \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longleftrightarrow> B \<lsq> C" by (rule MMI_breq1d)
   from S21 have S22: "A \<lsq> B \<longrightarrow> 
   B \<lsq> C \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C" by (rule MMI_biimprd)
   from S22 have S23: "A \<lsq> B \<longrightarrow> 
   A \<lsq> C \<and> B \<lsq> C \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C" by (rule MMI_adantld)
   have S24: "\<not>(A \<lsq> B) \<longrightarrow>  if(A \<lsq> B, B, A) = A" by (rule MMI_iffalse)
   from S24 have S25: "\<not>(A \<lsq> B) \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longleftrightarrow> A \<lsq> C" by (rule MMI_breq1d)
   from S25 have S26: "\<not>(A \<lsq> B) \<longrightarrow> 
   A \<lsq> C \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C" by (rule MMI_biimprd)
   from S26 have S27: "\<not>(A \<lsq> B) \<longrightarrow> 
   A \<lsq> C \<and> B \<lsq> C \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C" by (rule MMI_adantrd)
   from S23 S27 have S28: "A \<lsq> C \<and> B \<lsq> C \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C" by (rule MMI_pm2_61i)
   from S28 have S29: "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   A \<lsq> C \<and> B \<lsq> C \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C" by (rule MMI_a1i)
   from S19 S29 show "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> 
   ( if(A \<lsq> B, B, A)) \<lsq> C \<longleftrightarrow> A \<lsq> C \<and> B \<lsq> C" by (rule MMI_impbid)
qed

lemma (in MMIsar0) MMI_squeeze0: 
   shows "A \<in> \<real> \<and> \<zero> \<lsq> A \<and> (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<ls> A \<or> \<zero> = A" by (rule MMI_leloet)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> 
   \<zero> \<ls> A \<or> \<zero> = A" by (rule MMI_mpan)
   have S4: "A \<in> \<real> \<longrightarrow> \<not>(A \<ls> A)" by (rule MMI_ltnrt)
   from S4 have S5: "A \<in> \<real> \<longrightarrow> 
   A \<ls> A \<longrightarrow> A = \<zero>" by (rule MMI_pm2_21d)
   from S5 have S6: "A \<ls> A \<longrightarrow> 
   A \<in> \<real> \<longrightarrow> A = \<zero>" by (rule MMI_com12)
   from S6 have S7: "(\<zero> \<ls> A \<longrightarrow> A \<ls> A) \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   A \<in> \<real> \<longrightarrow> A = \<zero>" by (rule MMI_imim2i)
   from S7 have S8: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   (\<zero> \<ls> A \<longrightarrow> A \<ls> A) \<longrightarrow> A = \<zero>" by (rule MMI_com13)
   { fix x
     have S9: "x = A \<longrightarrow> 
       \<zero> \<ls> x \<longleftrightarrow> \<zero> \<ls> A" by (rule MMI_breq2)
     have S10: "x = A \<longrightarrow> 
       A \<ls> x \<longleftrightarrow> A \<ls> A" by (rule MMI_breq2)
     from S9 S10 have "x = A \<longrightarrow> 
       (\<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longleftrightarrow> 
       (\<zero> \<ls> A \<longrightarrow> A \<ls> A)" by (rule MMI_imbi12d)
   } then have S11: "\<forall> x.  x = A \<longrightarrow> 
       (\<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longleftrightarrow> 
       (\<zero> \<ls> A \<longrightarrow> A \<ls> A)" by simp
     from S11 have S12: "A \<in> \<real> \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> A \<ls> A" by (rule MMI_rcla4v)
   from S8 S12 have S13: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_syl5d)
   have S14: "A = \<zero> \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_ax_1)
   from S14 have S15: "\<zero> = A \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_eqcoms)
   from S15 have S16: "A \<in> \<real> \<longrightarrow> 
   \<zero> = A \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_a1i)
   from S13 S16 have S17: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<or> \<zero> = A \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_jaod)
   from S3 S17 have S18: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<longrightarrow> 
   (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_sylbid)
   from S18 show "A \<in> \<real> \<and> \<zero> \<lsq> A \<and> (\<forall>x\<in>\<real>. \<zero> \<ls> x \<longrightarrow> A \<ls> x) \<longrightarrow> A = \<zero>" by (rule MMI_3imp)
qed

(********* 490 ************************************)

(*** this is proven by hand, bc the definition of complex 
    naturals is different in Metamath than in MMIsar0
    **********************)

lemma (in MMIsar0) MMI_peano5nn: assumes "A=A"
  shows "( \<one>\<in>A \<and> (\<forall>x\<in>A. x\<ca>\<one> \<in> A ) ) \<longrightarrow> \<nat> \<subseteq> A"
proof -
 { assume A1: "\<one> \<in> A"  and A2: "\<forall>x. x\<in>A \<longrightarrow> x\<ca>\<one> \<in> A"
   let ?N = "A\<inter>\<real>"
   have "?N \<in> Pow(\<real>)" by auto
   moreover from A1 have "\<one> \<in> ?N" using MMI_ax1re by simp
   moreover from A2 have "\<forall>n. n\<in>?N \<longrightarrow> n\<ca>\<one> \<in> ?N"
     using MMI_ax1re MMI_axaddrcl by simp
   ultimately have "\<nat> \<subseteq> A" using cxn_def by auto
 } then show ?thesis by simp
qed

(********* 491-497 *******************************)


lemma (in MMIsar0) MMI_nnssre: 
   shows "\<nat> \<subseteq>\<real>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   { fix x
     have "x \<in> \<real> \<longrightarrow> x \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
   } then have S2: "\<forall>x. x \<in> \<real> \<longrightarrow> x \<ca> \<one> \<in> \<real>" by simp
   from S2 have S3: "\<forall>x\<in>\<real>. x \<ca> \<one> \<in> \<real>" by (rule MMI_rgen)
   have S4: "\<real> = \<real>" by (rule MMI_reex)
   from S4 have S5: "\<one> \<in> \<real> \<and> (\<forall>x\<in>\<real>. x \<ca> \<one> \<in> \<real>) \<longrightarrow> \<nat> \<subseteq>\<real>" by (rule MMI_peano5nn)
   from S1 S3 S5 show "\<nat> \<subseteq>\<real>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_nnsscn: 
   shows "\<nat> \<subseteq>\<complex>"
proof -
   have S1: "\<nat> \<subseteq>\<real>" by (rule MMI_nnssre)
   have S2: "\<real> \<subseteq>\<complex>" by (rule MMI_axresscn)
   from S1 S2 show "\<nat> \<subseteq>\<complex>" by (rule MMI_sstri)
qed

lemma (in MMIsar0) MMI_nnret: 
   shows "A \<in> \<nat> \<longrightarrow> A \<in> \<real>"
proof -
   have S1: "\<nat> \<subseteq>\<real>" by (rule MMI_nnssre)
   from S1 show "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_sseli)
qed

lemma (in MMIsar0) MMI_nncnt: 
   shows "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>"
proof -
   have S1: "\<nat> \<subseteq>\<complex>" by (rule MMI_nnsscn)
   from S1 show "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" by (rule MMI_sseli)
qed

lemma (in MMIsar0) MMI_nnre: assumes A1: "A \<in> \<nat>"   
   shows "A \<in> \<real>"
proof -
   from A1 have S1: "A \<in> \<nat>".
   have S2: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   from S1 S2 show "A \<in> \<real>" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_nncn: assumes A1: "A \<in> \<nat>"   
   shows "A \<in> \<complex>"
proof -
   from A1 have S1: "A \<in> \<nat>".
   from S1 have S2: "A \<in> \<real>" by (rule MMI_nnre)
   from S2 show "A \<in> \<complex>" by (rule MMI_recn)
qed

lemma (in MMIsar0) MMI_nnex: 
   shows "\<nat> = \<nat>"
proof -
   have S1: "\<real> = \<real>" by (rule MMI_reex)
   have S2: "\<nat> \<subseteq>\<real>" by (rule MMI_nnssre)
   from S1 S2 show "\<nat> = \<nat>" by (rule MMI_ssexi)
qed

(********* 498,499 **************************
    proven by hand to get us to 500 without modifying 
    mmisar Haskell source - parsing Metamath 
    set comprehension is not supported yet.*)

lemma MMI_helper1: assumes "\<Inter>K \<noteq> 0" shows "K\<noteq>0"
  using assms by auto

lemma (in MMIsar0) MMI_peano2nn:
  shows "x \<in> \<nat> \<longrightarrow> x\<ca>\<one> \<in> \<nat>"
proof -
  let ?K = "{N \<in> Pow(\<real>). \<one> \<in> N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"
  { assume A1: "x\<in>\<nat>"
    then have "\<Inter>?K \<noteq> 0" using cxn_def by auto
    then have "?K\<noteq>0" by (rule MMI_helper1)
    with A1 have "x\<ca>\<one> \<in> \<nat>" using cxn_def by auto
  } then show  "x \<in> \<nat> \<longrightarrow> x\<ca>\<one> \<in> \<nat>" by simp
qed

lemma (in MMIsar0) MMI_dfnn2: shows
  "\<nat> = \<Inter> {N \<in> Pow(\<real>). N \<subseteq> \<real> \<and> \<one>\<in>N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"
proof -
  let ?K\<^sub>1 = "{N \<in> Pow(\<real>). N \<subseteq> \<real> \<and> \<one>\<in>N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"
  let ?K\<^sub>2 = "{N \<in> Pow(\<real>). \<one>\<in>N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"
  have "?K\<^sub>1 = ?K\<^sub>2" by auto
  then show ?thesis using cxn_def by simp
qed

end
