(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2006-2009  Slawomir Kolodynski

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

section \<open>Metamath sampler\<close>

theory Metamath_Sampler imports Metamath_Interface MMI_Complex_ZF_2

begin

text\<open>The theorems translated from Metamath reside in the \<open>MMI_Complex_ZF\<close>,
  \<open>MMI_Complex_ZF_1\<close> and \<open>MMI_Complex_ZF_2\<close> theories. 
  The proofs of these theorems are very verbose and for this
  reason the theories are not shown in the proof document or the FormaMath.org 
  site. This theory file contains some examples of theorems 
  translated from Metamath and formulated in the \<open>complex0\<close> context.
  This serves two purposes: to give an overview of the material covered in
  the translated theorems and to provide examples of how to take a translated
  theorem (proven in the \<open>MMIsar0\<close> context) and transfer it to the 
  \<open>complex0\<close> context. The typical procedure for moving a theorem from
  \<open>MMIsar0\<close> to \<open>complex0\<close> is as follows:
  First we define certain aliases that map names defined in the \<open>complex0\<close>
  to their corresponding names in the \<open>MMIsar0\<close> context. This makes it 
  easy to copy and paste the statement of the theorem as 
  displayed with ProofGeneral. Then we run the Isabelle 
  from ProofGeneral up to the theorem we want to move. When the theorem is verified
  ProofGeneral displays the statement in the raw set theory notation, stripped 
  from any notation defined in the \<open>MMIsar0\<close> locale. This is what we copy
  to the proof in the \<open>complex0\<close> locale. After that we just can write 
  "then have ?thesis by simp" and the simplifier translates the raw set 
  theory notation to the one used in \<open>complex0\<close>.
\<close>

subsection\<open>Extended reals and order\<close>

text\<open>In this sectin we import a couple of theorems about the extended 
  real line and the linear order on it.\<close>

text\<open>Metamath uses the set of real numbers extended with $+\infty$ and $-\infty$. 
  The $+\infty$ and $-\infty$ symbols are defined quite arbitrarily as $\mathbb{C}$
  and $\mathbb{\{ C\} }$, respectively. The next lemma that corresponds to 
  Metamath's \<open>renfdisj\<close> states that $+\infty$ and $-\infty$ are not 
  elements of $\mathbb{R}$.\<close>

lemma (in complex0) renfdisj: shows "\<real> \<inter> {\<cpnf>,\<cmnf>} = 0"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have "?real \<inter> {?complex, {?complex}} = 0"
    by (rule MMIsar0.MMI_renfdisj)
  thus "\<real> \<inter> {\<cpnf>,\<cmnf>} = 0" by simp
qed
  
text\<open>The order relation used most often in Metamath is defined on 
  the set of complex reals extended with   $+\infty$ and $-\infty$. 
  The next lemma
  allows to use Metamath's \<open>xrltso\<close> that states that the \<open>\<ls>\<close>
  relations is a strict linear order on the extended set.\<close>

lemma (in complex0) xrltso: shows "\<cltrrset> Orders \<real>\<^sup>*"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have 
    "(?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
      {{?complex}} \<times> ?real) Orders (?real \<union> {?complex, {?complex}})"
    by (rule MMIsar0.MMI_xrltso)
  moreover have "?lessrrel \<inter> ?real \<times> ?real = ?lessrrel"
    using cplx_strict_ord_on_cplx_reals by auto
  ultimately show "\<cltrrset> Orders \<real>\<^sup>*" by simp
qed

text\<open>Metamath defines the usual $<$ and $\leq$ ordering relations for the
  extended real line, including $+\infty$ and $-\infty$.\<close>

lemma (in complex0) xrrebndt: assumes A1: "x \<in> \<real>\<^sup>*"
  shows "x \<in> \<real> \<longleftrightarrow> ( \<cmnf> \<ls> x \<and> x \<ls> \<cpnf> )"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have "x \<in> \<real> \<union> {\<complex>, {\<complex>}} \<longrightarrow>
    x \<in> \<real> \<longleftrightarrow> \<langle>{\<complex>}, x\<rangle> \<in> ?lessrrel \<inter> \<real> \<times> \<real> \<union> {\<langle>{\<complex>}, \<complex>\<rangle>} \<union> 
    \<real> \<times> {\<complex>} \<union> {{\<complex>}} \<times> \<real> \<and>
    \<langle>x, \<complex>\<rangle> \<in> ?lessrrel \<inter> \<real> \<times> \<real> \<union> {\<langle>{\<complex>}, \<complex>\<rangle>} \<union> 
    \<real> \<times> {\<complex>} \<union> {{\<complex>}} \<times> \<real>"
    by (rule MMIsar0.MMI_xrrebndt)
  then have "x \<in> \<real>\<^sup>* \<longrightarrow> ( x \<in> \<real> \<longleftrightarrow> ( \<cmnf> \<ls> x \<and> x \<ls> \<cpnf> ) )"
    by simp
  with A1 show ?thesis by simp
qed

text\<open>A quite involved inequality.\<close>

lemma (in complex0) lt2mul2divt: 
  assumes A1: "a \<in> \<real>"  "b \<in> \<real>"  "c \<in> \<real>"  "d \<in> \<real>" and
  A2: "\<zero> \<ls> b"  "\<zero> \<ls> d"
  shows "a\<cdot>b \<ls> c\<cdot>d \<longleftrightarrow> a\<cdiv>d \<ls> c\<cdiv>b"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have
    "(a \<in> ?real \<and> b \<in> ?real) \<and>
    (c \<in> ?real \<and> d \<in> ?real) \<and>
    \<langle>?zero, b\<rangle> \<in> ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real \<and>
    \<langle>?zero, d\<rangle> \<in> ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real \<longrightarrow>
    \<langle>?cmulset ` \<langle>a, b\<rangle>, ?cmulset ` \<langle>c, d\<rangle>\<rangle> \<in>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real \<longleftrightarrow>
    \<langle>\<Union>{x \<in> ?complex . ?cmulset ` \<langle>d, x\<rangle> = a}, 
    \<Union>{x \<in> ?complex . ?cmulset ` \<langle>b, x\<rangle> = c}\<rangle> \<in>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real" 
    by (rule MMIsar0.MMI_lt2mul2divt)
  with A1 A2 show ?thesis by simp
qed

text\<open>A real number is smaller than its half iff it is positive.\<close>

lemma (in complex0) halfpos: assumes A1: "a \<in> \<real>"
  shows "\<zero> \<ls> a \<longleftrightarrow> a\<cdiv>\<two> \<ls> a"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  from A1 have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    and "a \<in> ?real"
    using MMIsar_valid by auto
  then have
    "\<langle>?zero, a\<rangle> \<in>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real \<longleftrightarrow>
    \<langle>\<Union>{x \<in> ?complex . ?cmulset ` \<langle>?caddset ` \<langle>?one, ?one\<rangle>, x\<rangle> = a}, a\<rangle> \<in>
    ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real"
    by (rule MMIsar0.MMI_halfpos)
  then show ?thesis by simp
qed

text\<open>One more inequality.\<close>

lemma (in complex0) ledivp1t: 
  assumes A1:  "a \<in> \<real>"   "b \<in> \<real>" and
  A2: "\<zero> \<lsq> a"  "\<zero> \<lsq> b"
  shows "(a\<cdiv>(b \<ca> \<one>))\<cdot>b \<lsq> a"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have
    "(a \<in> ?real \<and> \<langle>a, ?zero\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real) \<and> 
    b \<in> ?real \<and> \<langle>b, ?zero\<rangle> \<notin> ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real \<longrightarrow>
    \<langle>a,?cmulset`\<langle>\<Union>{x \<in> ?complex . ?cmulset`\<langle>?caddset`\<langle>b, ?one\<rangle>, x\<rangle> = a}, b\<rangle>\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real"
    by (rule MMIsar0.MMI_ledivp1t)
  with A1 A2 show ?thesis by simp
qed

subsection\<open>Natural real numbers\<close>

text\<open>In standard mathematics natural numbers are treated as a subset of 
  real numbers.
  From the set theory point of view however those are quite different objects.
  In this section we talk about "real natural" numbers i.e. the conterpart of
  natural numbers that is a subset of the reals.\<close>

text\<open>Two ways of saying that there are no natural numbers between $n$ and $n+1$.\<close>

lemma (in complex0) no_nats_between: 
  assumes A1: "n \<in> \<nat>"  "k \<in> \<nat>"
  shows 
  "n\<lsq>k \<longleftrightarrow> n \<ls> k\<ca>\<one>"
  "n \<ls> k \<longleftrightarrow> n \<ca> \<one> \<lsq> k" 
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have I: "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have 
    "n \<in> \<Inter>{N \<in> Pow(?real) . ?one \<in> N \<and> 
    (\<forall>n. n \<in> N \<longrightarrow> ?caddset ` \<langle>n, ?one\<rangle> \<in> N)} \<and>
    k \<in> \<Inter>{N \<in> Pow(?real) . ?one \<in> N \<and> 
    (\<forall>n. n \<in> N \<longrightarrow> ?caddset ` \<langle>n, ?one\<rangle> \<in> N)} \<longrightarrow>
    \<langle>k, n\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real \<longleftrightarrow>
    \<langle>n, ?caddset ` \<langle>k, ?one\<rangle>\<rangle> \<in>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real" by (rule MMIsar0.MMI_nnleltp1t)
  then have "n \<in> \<nat> \<and> k \<in> \<nat> \<longrightarrow> n \<lsq> k \<longleftrightarrow> n \<ls> k \<ca> \<one>"
    by simp
  with A1 show "n\<lsq>k \<longleftrightarrow> n \<ls> k\<ca>\<one>" by simp
  from I have
    "n \<in> \<Inter>{N \<in> Pow(?real) . ?one \<in> N \<and> 
    (\<forall>n. n \<in> N \<longrightarrow> ?caddset ` \<langle>n, ?one\<rangle> \<in> N)} \<and>
    k \<in> \<Inter>{N \<in> Pow(?real) . ?one \<in> N \<and> 
    (\<forall>n. n \<in> N \<longrightarrow> ?caddset ` \<langle>n, ?one\<rangle> \<in> N)} \<longrightarrow>
    \<langle>n, k\<rangle> \<in>
    ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real \<longleftrightarrow>  \<langle>k, ?caddset ` \<langle>n, ?one\<rangle>\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real" by (rule MMIsar0.MMI_nnltp1let)
  then have "n \<in> \<nat> \<and> k \<in> \<nat> \<longrightarrow>  n \<ls> k \<longleftrightarrow> n \<ca> \<one> \<lsq> k"
    by simp
  with A1 show "n \<ls> k \<longleftrightarrow> n \<ca> \<one> \<lsq> k" by simp
qed

text\<open>Metamath has some very complicated and general version of induction
  on (complex) natural numbers that I can't even understand. As an exercise
  I derived a more standard version that is imported to the \<open>complex0\<close> 
  context below.\<close>

lemma (in complex0) cplx_nat_ind: assumes A1: "\<psi>(\<one>)" and 
  A2: "\<forall>k \<in> \<nat>. \<psi>(k) \<longrightarrow> \<psi>(k\<ca>\<one>)" and
  A3: "n \<in> \<nat>"
  shows "\<psi>(n)"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have I: "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  moreover from A1 A2 A3 have
    "\<psi>(?one)"
    "\<forall>k\<in>\<Inter>{N \<in> Pow(?real) . ?one \<in> N \<and> 
    (\<forall>n. n \<in> N \<longrightarrow> ?caddset ` \<langle>n, ?one\<rangle> \<in> N)}.
    \<psi>(k) \<longrightarrow> \<psi>(?caddset ` \<langle>k, ?one\<rangle>)"
    "n \<in> \<Inter>{N \<in> Pow(?real) . ?one \<in> N \<and> 
    (\<forall>n. n \<in> N \<longrightarrow> ?caddset ` \<langle>n, ?one\<rangle> \<in> N)}"
    by auto
  ultimately show "\<psi>(n)" by (rule MMIsar0.nnind1)
qed

text\<open>Some simple arithmetics.\<close>

lemma (in complex0) arith: shows
  "\<two> \<ca> \<two> = \<four>"
  "\<two>\<cdot>\<two> = \<four>"
  "\<three>\<cdot>\<two> = \<six>"
  "\<three>\<cdot>\<three> = \<nine>"
proof -
  let ?real = "\<real>"
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have I: "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have
    "?caddset ` \<langle>?caddset ` \<langle>?one, ?one\<rangle>, ?caddset ` \<langle>?one, ?one\<rangle>\<rangle> =
    ?caddset ` \<langle>?caddset ` \<langle>?caddset ` \<langle>?one, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>"
    by (rule MMIsar0.MMI_2p2e4)
  thus "\<two> \<ca> \<two> = \<four>" by simp
  from I have
    "?cmulset`\<langle>?caddset`\<langle>?one, ?one\<rangle>, ?caddset`\<langle>?one, ?one\<rangle>\<rangle> =
    ?caddset`\<langle>?caddset`\<langle>?caddset`\<langle>?one, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>"
    by (rule MMIsar0.MMI_2t2e4)
  thus "\<two>\<cdot>\<two> = \<four>" by simp
  from I have
    "?cmulset`\<langle>?caddset`\<langle>?caddset`\<langle>?one, ?one\<rangle>, ?one\<rangle>, ?caddset`\<langle>?one, ?one\<rangle>\<rangle> =
    ?caddset `\<langle>?caddset`\<langle>?caddset`\<langle>?caddset`\<langle>?caddset`
    \<langle>?one, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>"
    by (rule MMIsar0.MMI_3t2e6)
  thus "\<three>\<cdot>\<two> = \<six>" by simp
  from I have "?cmulset `
    \<langle>?caddset`\<langle>?caddset`\<langle>?one, ?one\<rangle>, ?one\<rangle>,
    ?caddset`\<langle>?caddset`\<langle>?one, ?one\<rangle>, ?one\<rangle>\<rangle> =
    ?caddset`\<langle>?caddset`\<langle>?caddset `\<langle>?caddset `
    \<langle>?caddset`\<langle>?caddset`\<langle>?caddset`\<langle>?caddset`\<langle>?one, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>,
    ?one\<rangle>, ?one\<rangle>, ?one\<rangle>, ?one\<rangle>"
    by (rule MMIsar0.MMI_3t3e9)
  thus "\<three>\<cdot>\<three> = \<nine>" by simp
qed

subsection\<open>Infimum and supremum in real numbers\<close>

text\<open>Real numbers form a complete ordered field. Here we import a couple
  of Metamath theorems about supremu and infimum.\<close>

text\<open>If a set $S$ has a smallest element, then the infimum of $S$ belongs
  to it.\<close>

lemma (in complex0) lbinfmcl: assumes A1: "S \<subseteq> \<real>" and 
  A2: "\<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y"
  shows  "Infim(S,\<real>,\<cltrrset>) \<in> S"
proof -
  let ?real = "\<real>" 
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have I: "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have
    "S \<subseteq> ?real \<and> (\<exists>x\<in>S. \<forall>y\<in>S. \<langle>y, x\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union>
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real) \<longrightarrow>
    Sup(S, ?real,  
    converse(?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real)) \<in> S"
    by (rule MMIsar0.MMI_lbinfmcl)
  then have 
    "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow>  
    Sup(S,\<real>,converse(\<cltrrset>)) \<in> S" by simp
  with A1 A2 show ?thesis using Infim_def by simp
qed

text\<open>Supremum of any subset of reals that is bounded above is real.\<close>

lemma (in complex0) sup_is_real: 
  assumes "A \<subseteq> \<real> " and "A \<noteq> 0" and "\<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x"
  shows "Sup(A,\<real>,\<cltrrset>) \<in> \<real>"  
proof -
  let ?real = "\<real>" 
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have 
    "A \<subseteq> ?real \<and> A \<noteq> 0 \<and> (\<exists>x\<in>?real.  \<forall>y\<in>A. \<langle>x, y\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real) \<longrightarrow> 
    Sup(A, ?real,
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real) \<in> ?real" 
    by (rule MMIsar0.MMI_suprcl)
  with assms show ?thesis by simp
qed

text\<open>If a real number is smaller that the supremum of $A$, then 
  we can find an element of $A$ greater than it.\<close>

lemma (in complex0) suprlub: 
  assumes "A \<subseteq>\<real>" and "A \<noteq> 0" and "\<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x" 
  and "B \<in> \<real>"  and "B \<ls> Sup(A,\<real>,\<cltrrset>)"
  shows "\<exists>z\<in>A. B \<ls> z"
proof -
  let ?real = "\<real>" 
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have "(A \<subseteq> ?real \<and> A \<noteq> 0 \<and> (\<exists>x\<in>?real. \<forall>y\<in>A. \<langle>x, y\<rangle> \<notin>
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> 
    {{?complex}} \<times> ?real)) \<and> B \<in> ?real \<and> \<langle>B, Sup(A, ?real,
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real)\<rangle> \<in> ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real \<longrightarrow>
    (\<exists>z\<in>A. \<langle>B, z\<rangle> \<in> ?lessrrel \<inter> ?real \<times> ?real \<union> 
    {\<langle>{?complex}, ?complex\<rangle>} \<union> ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real)"
    by (rule MMIsar0.MMI_suprlub)
  with assms show ?thesis by simp
qed

text\<open>Something a bit more interesting: infimum of a set that is bounded
  below is real and equal to the
  minus supremum of the set flipped around zero.\<close>

lemma (in complex0) infmsup: 
  assumes "A \<subseteq> \<real>" and "A \<noteq> 0" and "\<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y"
  shows
  "Infim(A,\<real>,\<cltrrset>) \<in> \<real>"
  "Infim(A,\<real>,\<cltrrset>) = ( \<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>) )"
proof -
  let ?real = "\<real>" 
  let ?complex = "\<complex>"
  let ?one = "\<one>"
  let ?zero = "\<zero>"
  let ?iunit = "\<i>"
  let ?caddset = "CplxAdd(R,A)"
  let ?cmulset = "CplxMul(R,A,M)"
  let ?lessrrel = "StrictVersion(CplxROrder(R,A,r))"
  have I: "MMIsar0
    (?real, ?complex, ?one, ?zero, ?iunit, ?caddset, ?cmulset, ?lessrrel)"
    using MMIsar_valid by simp
  then have
    "A \<subseteq> ?real \<and> A \<noteq> 0 \<and> (\<exists>x\<in>?real. \<forall>y\<in>A. \<langle>y, x\<rangle> \<notin> 
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real) \<longrightarrow> Sup(A, ?real, converse
    (?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real)) =
    \<Union>{x \<in> ?complex . ?caddset`
    \<langle>Sup({z \<in> ?real . \<Union>{x \<in> ?complex . ?caddset`\<langle>z, x\<rangle> = ?zero} \<in> A}, ?real,
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real), x\<rangle> = ?zero}"
    by (rule MMIsar0.MMI_infmsup)
  then have "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
    Sup(A,\<real>,converse(\<cltrrset>)) = ( \<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>) )"
    by simp
  with assms show
    "Infim(A,\<real>,\<cltrrset>) = ( \<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>) )"
    using Infim_def by simp
  from I have
    "A \<subseteq> ?real \<and> A \<noteq> 0 \<and> (\<exists>x\<in>?real. \<forall>y\<in>A. \<langle>y, x\<rangle> \<notin> 
    ?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union>
    {{?complex}} \<times> ?real) \<longrightarrow> Sup(A, ?real, converse
    (?lessrrel \<inter> ?real \<times> ?real \<union> {\<langle>{?complex}, ?complex\<rangle>} \<union> 
    ?real \<times> {?complex} \<union> {{?complex}} \<times> ?real)) \<in> ?real"
    by (rule MMIsar0.MMI_infmrcl)
  with assms show "Infim(A,\<real>,\<cltrrset>) \<in> \<real>"
    using Infim_def by simp
qed

end
