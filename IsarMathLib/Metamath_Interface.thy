(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2006  Slawomir Kolodynski

This program is free software; Redistribution and use in source and binary forms, 
with or without modification, are permitted provided that the 
following conditions are met:

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Metamath interface\<close>

theory Metamath_Interface imports Complex_ZF MMI_prelude

begin

text\<open>This theory contains some lemmas that make it possible to use 
  the theorems translated from Metamath in a the \<open>complex0\<close> 
  context.\<close>

subsection\<open>MMisar0 and complex0 contexts.\<close>

text\<open>In the section we show a lemma that the assumptions in 
   \<open>complex0\<close> context imply the assumptions of the \<open>MMIsar0\<close>
   context. The \<open>Metamath_sampler\<close> theory provides examples 
   how this lemma can be used.\<close>

text\<open>The next lemma states that we can use 
  the theorems proven in the \<open>MMIsar0\<close> context in
  the \<open>complex0\<close> context. Unfortunately we have to 
  use low level Isabelle methods "rule" and "unfold" in the proof, simp
  and blast fail on the order axioms.
\<close>


lemma (in complex0) MMIsar_valid: 
  shows "MMIsar0(\<real>,\<complex>,\<one>,\<zero>,\<i>,CplxAdd(R,A),CplxMul(R,A,M),
  StrictVersion(CplxROrder(R,A,r)))"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?zero = "\<zero>"
  let ?one = "\<one>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "(\<forall>a b. a \<in> ?real \<and> b \<in> ?real \<longrightarrow>
    \<langle>a, b\<rangle> \<in> ?lessrrel \<longleftrightarrow> \<not> (a = b \<or> \<langle>b, a\<rangle> \<in> ?lessrrel))"
  proof -
    have I:
      "\<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> (a \<lsr> b \<longleftrightarrow> \<not>(a=b \<or> b \<lsr> a))"
      using pre_axlttri by blast
    { fix a b assume "a \<in> ?real \<and> b \<in> ?real"
      with I have "(a \<lsr> b \<longleftrightarrow> \<not>(a=b \<or> b \<lsr> a))"
	by blast
      hence
	"\<langle>a, b\<rangle> \<in> ?lessrrel \<longleftrightarrow> \<not> (a = b \<or> \<langle>b, a\<rangle> \<in> ?lessrrel)"
	by simp
    } thus "(\<forall>a b. a \<in> ?real \<and> b \<in> ?real \<longrightarrow>
	(\<langle>a, b\<rangle> \<in> ?lessrrel \<longleftrightarrow> \<not> (a = b \<or> \<langle>b, a\<rangle> \<in> ?lessrrel)))"
      by blast
  qed
  moreover
  have "(\<forall>a b c.
    a \<in> ?real \<and> b \<in> ?real \<and> c \<in> ?real \<longrightarrow>
    \<langle>a, b\<rangle> \<in> ?lessrrel \<and> \<langle>b, c\<rangle> \<in> ?lessrrel \<longrightarrow> \<langle>a, c\<rangle> \<in> ?lessrrel)"
  proof -
    have II: "\<forall>a b c.  a \<in> \<real> \<and> b \<in> \<real> \<and> c \<in> \<real> \<longrightarrow> 
      ((a \<lsr> b \<and> b \<lsr> c) \<longrightarrow> a \<lsr> c)"
      using pre_axlttrn by blast
    { fix a b c assume "a \<in> ?real \<and> b \<in> ?real \<and> c \<in> ?real"
      with II have "(a \<lsr> b \<and> b \<lsr> c) \<longrightarrow> a \<lsr> c"
	by blast
      hence 	
	"\<langle>a, b\<rangle> \<in> ?lessrrel \<and> \<langle>b, c\<rangle> \<in> ?lessrrel \<longrightarrow> \<langle>a, c\<rangle> \<in> ?lessrrel"
	by simp
    } thus  "(\<forall>a b c.
	a \<in> ?real \<and> b \<in> ?real \<and> c \<in> ?real \<longrightarrow>
	\<langle>a, b\<rangle> \<in> ?lessrrel \<and> \<langle>b, c\<rangle> \<in> ?lessrrel \<longrightarrow> \<langle>a, c\<rangle> \<in> ?lessrrel)"
      by blast
  qed
  moreover have "(\<forall>A B C.
    A \<in> ?real \<and> B \<in> ?real \<and> C \<in> ?real \<longrightarrow>
    \<langle>A, B\<rangle> \<in> ?lessrrel \<longrightarrow>
    \<langle>?caddset ` \<langle>C, A\<rangle>, ?caddset ` \<langle>C, B\<rangle>\<rangle> \<in> ?lessrrel)"
    using pre_axltadd by simp
  moreover have "(\<forall>A B. A \<in> ?real \<and> B \<in> ?real \<longrightarrow>
    \<langle>?zero, A\<rangle> \<in> ?lessrrel \<and> \<langle>?zero, B\<rangle> \<in> ?lessrrel \<longrightarrow>
    \<langle>?zero, ?cmulset ` \<langle>A, B\<rangle>\<rangle> \<in> ?lessrrel)"
    using pre_axmulgt0 by simp
  moreover have 
    "(\<forall>S. S \<subseteq> ?real \<and> S \<noteq> 0 \<and> (\<exists>x\<in>?real. \<forall>y\<in>S. \<langle>y, x\<rangle> \<in> ?lessrrel) \<longrightarrow>
    (\<exists>x\<in>?real.
    (\<forall>y\<in>S. \<langle>x, y\<rangle> \<notin> ?lessrrel) \<and>
    (\<forall>y\<in>?real. \<langle>y, x\<rangle> \<in> ?lessrrel \<longrightarrow> (\<exists>z\<in>S. \<langle>y, z\<rangle> \<in> ?lessrrel))))"
    using pre_axsup by simp
  moreover have "\<real> \<subseteq> \<complex>" using axresscn by simp
  moreover have "\<one> \<noteq> \<zero>" using ax1ne0 by simp
  moreover have "\<complex> isASet" by simp
  moreover have " CplxAdd(R,A) : \<complex> \<times> \<complex> \<rightarrow> \<complex>" 
    using axaddopr by simp
  moreover have "CplxMul(R,A,M) : \<complex> \<times> \<complex> \<rightarrow> \<complex>" 
    using axmulopr by simp
  moreover have 
    "\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> a\<cdot> b = b \<cdot> a"
    using axmulcom by simp
  hence "(\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow>
          ?cmulset ` \<langle>a, b\<rangle> = ?cmulset ` \<langle>b, a\<rangle>
    )" by simp
  moreover have "\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> a \<ca> b \<in> \<complex>"
    using axaddcl by simp
  hence "(\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> 
          ?caddset ` \<langle>a, b\<rangle> \<in> \<complex>
      )" by simp
  moreover have "\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> a \<cdot> b \<in> \<complex>"
    using axmulcl by simp
  hence "(\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> 
    ?cmulset ` \<langle>a, b\<rangle> \<in> \<complex> )" by simp
  moreover have 
    "\<forall>a b C. a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> 
    a \<cdot> (b \<ca> C) = a \<cdot> b \<ca> a \<cdot> C"
    using axdistr by simp
  hence "\<forall>a b C.
         a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
         ?cmulset ` \<langle>a, ?caddset ` \<langle>b, C\<rangle>\<rangle> =
         ?caddset `
         \<langle>?cmulset ` \<langle>a, b\<rangle>, ?cmulset ` \<langle>a, C\<rangle>\<rangle>" 
    by simp
  moreover have "\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow>
         a \<ca> b = b \<ca> a"
    using axaddcom by simp
  hence "\<forall>a b.
          a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow>
          ?caddset ` \<langle>a, b\<rangle> = ?caddset ` \<langle>b, a\<rangle>" by simp
  moreover have "\<forall>a b C. a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
      a \<ca> b \<ca> C = a \<ca> (b \<ca> C)"
    using axaddass by simp
  hence "\<forall>a b C.
          a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
          ?caddset ` \<langle>?caddset ` \<langle>a, b\<rangle>, C\<rangle> =
          ?caddset ` \<langle>a, ?caddset ` \<langle>b, C\<rangle>\<rangle>" by simp
  moreover have 
    "\<forall>a b c. a \<in> \<complex> \<and> b \<in> \<complex> \<and> c \<in> \<complex> \<longrightarrow> a\<cdot>b\<cdot>c = a\<cdot>(b\<cdot>c)"
    using axmulass by simp
  hence "\<forall>a b C.
          a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
          ?cmulset ` \<langle>?cmulset ` \<langle>a, b\<rangle>, C\<rangle> =
          ?cmulset ` \<langle>a, ?cmulset ` \<langle>b, C\<rangle>\<rangle>" by simp
  moreover have "\<one> \<in> \<real>" using ax1re by simp
  moreover have "\<i>\<cdot>\<i> \<ca> \<one> = \<zero>"
    using axi2m1 by simp
  hence "?caddset ` \<langle>?cmulset ` \<langle>\<i>, \<i>\<rangle>, \<one>\<rangle> = \<zero>" by simp
  moreover have "\<forall>a. a \<in> \<complex> \<longrightarrow> a \<ca> \<zero> = a"
    using ax0id by simp
  hence "\<forall>a. a \<in> \<complex> \<longrightarrow> ?caddset ` \<langle>a, \<zero>\<rangle> = a" by simp
  moreover have "\<i> \<in> \<complex>" using axicn by simp
  moreover have "\<forall>a. a \<in> \<complex> \<longrightarrow> (\<exists>x\<in>\<complex>. a \<ca> x = \<zero>)"
    using axnegex by simp
  hence "\<forall>a. a \<in> \<complex> \<longrightarrow> 
    (\<exists>x\<in>\<complex>. ?caddset ` \<langle>a, x\<rangle> = \<zero>)" by simp
  moreover have "\<forall>a. a \<in> \<complex> \<and> a \<noteq> \<zero> \<longrightarrow> (\<exists>x\<in>\<complex>. a \<cdot> x = \<one>)"
    using axrecex by simp
  hence "\<forall>a. a \<in> \<complex> \<and> a \<noteq> \<zero> \<longrightarrow> 
      ( \<exists>x\<in>\<complex>. ?cmulset ` \<langle>a, x\<rangle> = \<one> )" by simp
  moreover have "\<forall>a. a \<in> \<complex> \<longrightarrow> a\<cdot>\<one> = a"
    using ax1id by simp
 hence " \<forall>a. a \<in> \<complex> \<longrightarrow> 
        ?cmulset ` \<langle>a, \<one>\<rangle> = a" by simp
 moreover have "\<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> a \<ca> b \<in> \<real>"
   using axaddrcl by simp
 hence "\<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> 
     ?caddset ` \<langle>a, b\<rangle> \<in> \<real>" by simp
 moreover have "\<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> a \<cdot> b \<in> \<real>"
   using axmulrcl by simp
 hence "\<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> 
     ?cmulset ` \<langle>a, b\<rangle> \<in> \<real>" by simp
 moreover have "\<forall>a. a \<in> \<real> \<longrightarrow> (\<exists>x\<in>\<real>. a \<ca> x = \<zero>)"
   using axrnegex by simp
 hence "\<forall>a. a \<in> \<real> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. ?caddset ` \<langle>a, x\<rangle> = \<zero> )" by simp
 moreover have "\<forall>a. a \<in> \<real> \<and> a\<noteq>\<zero> \<longrightarrow> (\<exists>x\<in>\<real>. a \<cdot> x = \<one>)"
   using axrrecex by simp
 hence "\<forall>a. a \<in> \<real> \<and> a \<noteq> \<zero> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. ?cmulset ` \<langle>a, x\<rangle> = \<one>)" by simp
 
  ultimately have 
"(
   (
      (
         ( \<forall>a b.
           a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow>
           \<langle>a, b\<rangle> \<in> ?lessrrel \<longleftrightarrow>
           \<not> (a = b \<or> \<langle>b, a\<rangle> \<in> ?lessrrel)
         ) \<and>
       
         ( \<forall>a b C.
           a \<in> \<real> \<and> b \<in> \<real> \<and> C \<in> \<real> \<longrightarrow>
           \<langle>a, b\<rangle> \<in> ?lessrrel \<and>
           \<langle>b, C\<rangle> \<in> ?lessrrel \<longrightarrow>
           \<langle>a, C\<rangle> \<in> ?lessrrel
         ) \<and>
       
         (\<forall>a b C.
           a \<in> \<real> \<and> b \<in> \<real> \<and> C \<in> \<real> \<longrightarrow>
           \<langle>a, b\<rangle> \<in> ?lessrrel \<longrightarrow>
           \<langle>?caddset ` \<langle>C, a\<rangle>, ?caddset ` \<langle>C, b\<rangle>\<rangle> \<in>
           ?lessrrel
         )
      ) \<and>
           
      (
         ( \<forall>a b.
           a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow>
           \<langle>\<zero>, a\<rangle> \<in> ?lessrrel \<and>
           \<langle>\<zero>, b\<rangle> \<in> ?lessrrel \<longrightarrow>
           \<langle>\<zero>, ?cmulset ` \<langle>a, b\<rangle>\<rangle> \<in>
           ?lessrrel
         ) \<and>
           
         ( \<forall>S. S \<subseteq> \<real> \<and> S \<noteq> 0 \<and>
             ( \<exists>x\<in>\<real>. \<forall>y\<in>S. \<langle>y, x\<rangle> \<in> ?lessrrel
             ) \<longrightarrow>
             ( \<exists>x\<in>\<real>. 
                ( \<forall>y\<in>S. \<langle>x, y\<rangle> \<notin> ?lessrrel
                ) \<and>
                ( \<forall>y\<in>\<real>. \<langle>y, x\<rangle> \<in> ?lessrrel \<longrightarrow>
                   ( \<exists>z\<in>S. \<langle>y, z\<rangle> \<in> ?lessrrel
                   )
                )
             )
         )
      ) \<and>
      
      \<real> \<subseteq> \<complex> \<and> 
      \<one> \<noteq> \<zero>
   ) \<and>
      
   ( \<complex> isASet \<and> ?caddset \<in> \<complex> \<times> \<complex> \<rightarrow> \<complex> \<and> 
    ?cmulset \<in> \<complex> \<times> \<complex> \<rightarrow> \<complex>
   ) \<and>
   
   (
      (\<forall>a b.
          a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow>
          ?cmulset ` \<langle>a, b\<rangle> = ?cmulset ` \<langle>b, a\<rangle>
      ) \<and>
      
      (\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> 
          ?caddset ` \<langle>a, b\<rangle> \<in> \<complex>
      )
     
   ) \<and>
     
   (\<forall>a b. a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow> 
      ?cmulset ` \<langle>a, b\<rangle> \<in> \<complex>
   ) \<and>
     
   (\<forall>a b C.
         a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
         ?cmulset ` \<langle>a, ?caddset ` \<langle>b, C\<rangle>\<rangle> =
         ?caddset `
         \<langle>?cmulset ` \<langle>a, b\<rangle>, ?cmulset ` \<langle>a, C\<rangle>\<rangle>
   )
) \<and>


(
   (
      (\<forall>a b.
          a \<in> \<complex> \<and> b \<in> \<complex> \<longrightarrow>
          ?caddset ` \<langle>a, b\<rangle> = ?caddset ` \<langle>b, a\<rangle>
      ) \<and>
      
      (\<forall>a b C.
          a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
          ?caddset ` \<langle>?caddset ` \<langle>a, b\<rangle>, C\<rangle> =
          ?caddset ` \<langle>a, ?caddset ` \<langle>b, C\<rangle>\<rangle>
      ) \<and>
      
      (\<forall>a b C.
          a \<in> \<complex> \<and> b \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow>
          ?cmulset ` \<langle>?cmulset ` \<langle>a, b\<rangle>, C\<rangle> =
          ?cmulset ` \<langle>a, ?cmulset ` \<langle>b, C\<rangle>\<rangle>
      )
   ) \<and>
   
   
   (\<one> \<in> \<real> \<and> 
    ?caddset ` \<langle>?cmulset ` \<langle>\<i>, \<i>\<rangle>, \<one>\<rangle> = \<zero>
   ) \<and>
   
   (\<forall>a. a \<in> \<complex> \<longrightarrow> ?caddset ` \<langle>a, \<zero>\<rangle> = a
   ) \<and>
    
   \<i> \<in> \<complex>
) \<and>
   
(
   (\<forall>a. a \<in> \<complex> \<longrightarrow> 
      (\<exists>x\<in>\<complex>. ?caddset ` \<langle>a, x\<rangle> = \<zero>
      )
   ) \<and>
      
   ( \<forall>a. a \<in> \<complex> \<and> a \<noteq> \<zero> \<longrightarrow> 
      ( \<exists>x\<in>\<complex>. ?cmulset ` \<langle>a, x\<rangle> = \<one>
      )
   ) \<and>
   
   ( \<forall>a. a \<in> \<complex> \<longrightarrow> 
        ?cmulset ` \<langle>a, \<one>\<rangle> = a
   )
) \<and>
   
(
   ( \<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> 
     ?caddset ` \<langle>a, b\<rangle> \<in> \<real>
   ) \<and>
      
   ( \<forall>a b. a \<in> \<real> \<and> b \<in> \<real> \<longrightarrow> 
     ?cmulset ` \<langle>a, b\<rangle> \<in> \<real>
   )
) \<and>
    
( \<forall>a. a \<in> \<real> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. ?caddset ` \<langle>a, x\<rangle> = \<zero>
   ) 
) \<and>
   
( \<forall>a. a \<in> \<real> \<and> a \<noteq> \<zero> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. ?cmulset ` \<langle>a, x\<rangle> = \<one>
   )
)"
  by blast
then show "MMIsar0(\<real>,\<complex>,\<one>,\<zero>,\<i>,CplxAdd(R,A),CplxMul(R,A,M),
  StrictVersion(CplxROrder(R,A,r)))" unfolding MMIsar0_def by blast
qed
  

end
