(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005, 2006  Slawomir Kolodynski

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

section \<open>Division on integers\<close>

theory IntDiv_ZF_IML imports Int_ZF_1 ZF.IntDiv

begin

text\<open>This theory translates some results form the Isabelle's 
  \<open>IntDiv.thy\<close> theory to the notation used by IsarMathLib.\<close>

subsection\<open>Quotient and reminder\<close>

text\<open>For any integers $m,n$ , $n>0$ there are unique integers $q,p$
  such that $0\leq p < n$ and $m = n\cdot q + p$. Number $p$ in this 
  decompsition is usually called $m$ mod $n$. Standard Isabelle denotes numbers
  $q,p$ as \<open>m zdiv n\<close> and \<open>m zmod n\<close>, resp., 
  and we will use the same notation.\<close>

text\<open>The next lemma is sometimes called the "quotient-reminder theorem".\<close>

lemma (in int0) IntDiv_ZF_1_L1: assumes "m\<in>\<int>"  "n\<in>\<int>"
  shows "m = n\<cdot>(m zdiv n) \<ra> (m zmod n)"
  using assms Int_ZF_1_L2 raw_zmod_zdiv_equality
  by simp

text\<open>If $n$ is greater than $0$ then \<open>m zmod n\<close> is between $0$ and $n-1$.\<close>

lemma (in int0) IntDiv_ZF_1_L2: 
  assumes A1: "m\<in>\<int>" and A2: "\<zero>\<lsq>n"  "n\<noteq>\<zero>"
  shows 
  "\<zero> \<lsq> m zmod n"  
  "m zmod n \<lsq> n"    "m zmod n \<noteq> n" 
  "m zmod n \<lsq> n\<rs>\<one>"
proof -
  from A2 have T: "n \<in> \<int>"
    using Int_ZF_2_L1A by simp
  from A2 have "#0 $< n" using Int_ZF_2_L9 Int_ZF_1_L8 
    by auto
  with T show 
    "\<zero> \<lsq> m zmod n"  
    "m zmod n \<lsq> n"  
    "m zmod n \<noteq> n" 
    using pos_mod Int_ZF_1_L8 Int_ZF_1_L8A zmod_type 
      Int_ZF_2_L1 Int_ZF_2_L9AA 
    by auto
  then show "m zmod n \<lsq> n\<rs>\<one>"
    using Int_ZF_4_L1B by auto
qed

text\<open>$(m\cdot k)$ div $k = m$.\<close>

lemma (in int0) IntDiv_ZF_1_L3: 
  assumes "m\<in>\<int>"  "k\<in>\<int>"  and "k\<noteq>\<zero>"
  shows 
  "(m\<cdot>k) zdiv k = m"
  "(k\<cdot>m) zdiv k = m"
  using assms zdiv_zmult_self1 zdiv_zmult_self2 
    Int_ZF_1_L8 Int_ZF_1_L2 by auto

text\<open>The next lemma essentially translates \<open>zdiv_mono1\<close> from 
  standard Isabelle to our notation.\<close>

lemma (in int0) IntDiv_ZF_1_L4: 
  assumes A1: "m \<lsq> k" and A2: "\<zero>\<lsq>n"  "n\<noteq>\<zero>"
  shows "m zdiv n \<lsq>  k zdiv n"
proof -
  from A2 have "#0 \<lsq> n"  "#0 \<noteq> n"
    using Int_ZF_1_L8 by auto
  with A1 have 
    "m zdiv n $\<le> k zdiv n"
    "m zdiv n \<in> \<int>"    "m zdiv k \<in> \<int>"
    using Int_ZF_2_L1A Int_ZF_2_L9 zdiv_mono1
    by auto
  then show "(m zdiv n) \<lsq> (k zdiv n)"
    using Int_ZF_2_L1 by simp
qed

text\<open>A quotient-reminder theorem about integers greater than a given 
  product.\<close>

lemma (in int0) IntDiv_ZF_1_L5:
  assumes A1: "n \<in> \<int>\<^sub>+" and A2: "n \<lsq> k" and A3: "k\<cdot>n \<lsq> m" 
  shows 
  "m = n\<cdot>(m zdiv n) \<ra> (m zmod n)"
  "m = (m zdiv n)\<cdot>n \<ra> (m zmod n)"
  "(m zmod n) \<in> \<zero>..(n\<rs>\<one>)"
  "k \<lsq> (m zdiv n)"  
  "m zdiv n \<in> \<int>\<^sub>+"
proof -
  from A2 A3 have T: 
    "m\<in>\<int>"  "n\<in>\<int>"  "k\<in>\<int>"  "m zdiv n \<in> \<int>"  
    using Int_ZF_2_L1A by auto
   then show "m = n\<cdot>(m zdiv n) \<ra> (m zmod n)"
     using IntDiv_ZF_1_L1 by simp
   with T show "m = (m zdiv n)\<cdot>n \<ra> (m zmod n)"
     using Int_ZF_1_L4 by simp
    from A1 have I: "\<zero>\<lsq>n"  "n\<noteq>\<zero>"
     using PositiveSet_def by auto
   with T show "(m zmod n) \<in> \<zero>..(n\<rs>\<one>)"
    using IntDiv_ZF_1_L2 Order_ZF_2_L1
    by simp
  from A3 I have "(k\<cdot>n zdiv n) \<lsq> (m zdiv n)"
    using IntDiv_ZF_1_L4 by simp
  with I T show "k \<lsq> (m zdiv n)"
    using IntDiv_ZF_1_L3 by simp
  with A1 A2 show "m zdiv n \<in> \<int>\<^sub>+"
    using Int_ZF_1_5_L7 by blast
qed

  
end