(*    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2009  Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Integers 3\<close>

theory Int_ZF_3 imports Int_ZF_2

begin

text\<open>This theory is a continuation of \<open>Int_ZF_2\<close>. We consider 
  here the properties of slopes (almost homomorphisms on integers)
  that allow to define the order relation and multiplicative
  inverse on real numbers. We also prove theorems that allow to show 
  completeness of the order relation of real numbers we define in \<open>Real_ZF\<close>.
\<close>

subsection\<open>Positive slopes\<close>

text\<open>This section provides background material for defining the order relation on real numbers.\<close>

text\<open>Positive slopes are functions (of course.)\<close>

lemma (in int1) Int_ZF_2_3_L1: assumes A1: "f\<in>\<S>\<^sub>+" shows "f:\<int>\<rightarrow>\<int>"
  using assms AlmostHoms_def PositiveSet_def by simp

text\<open>A small technical lemma to simplify the proof of the next theorem.\<close>

lemma (in int1) Int_ZF_2_3_L1A: 
  assumes A1: "f\<in>\<S>\<^sub>+" and A2: "\<exists>n \<in> f``(\<int>\<^sub>+) \<inter> \<int>\<^sub>+. a\<lsq>n"
  shows "\<exists>M\<in>\<int>\<^sub>+. a \<lsq> f`(M)"
proof -
 from A1 have "f:\<int>\<rightarrow>\<int>"  "\<int>\<^sub>+ \<subseteq> \<int>" 
    using AlmostHoms_def PositiveSet_def by auto
 with A2 show ?thesis using func_imagedef by auto
qed

text\<open>The next lemma is Lemma 3 in the Arthan's paper.\<close>

lemma (in int1) Arthan_Lem_3: 
  assumes A1: "f\<in>\<S>\<^sub>+" and A2: "D \<in> \<int>\<^sub>+"
  shows "\<exists>M\<in>\<int>\<^sub>+. \<forall>m\<in>\<int>\<^sub>+. (m\<ra>\<one>)\<cdot>D \<lsq> f`(m\<cdot>M)" 
proof -
  let ?E = "max\<delta>(f) \<ra> D"
  let ?A = "f``(\<int>\<^sub>+) \<inter> \<int>\<^sub>+"
  from A1 A2 have I: "D\<lsq>?E"
    using Int_ZF_1_5_L3 Int_ZF_2_1_L8 Int_ZF_2_L1A Int_ZF_2_L15D
    by simp
  from A1 A2 have "?A \<subseteq> \<int>\<^sub>+"  "?A \<notin> Fin(\<int>)"  "\<two>\<cdot>?E \<in> \<int>" 
    using int_two_three_are_int Int_ZF_2_1_L8 PositiveSet_def Int_ZF_1_1_L5
    by auto
  with A1 have "\<exists>M\<in>\<int>\<^sub>+.  \<two>\<cdot>?E \<lsq> f`(M)"
    using Int_ZF_1_5_L2A Int_ZF_2_3_L1A by simp
  then obtain M where II: "M\<in>\<int>\<^sub>+"  and III: "\<two>\<cdot>?E \<lsq> f`(M)"
    by auto
  { fix m assume "m\<in>\<int>\<^sub>+" then have A4: "\<one>\<lsq>m"
      using Int_ZF_1_5_L3 by simp
    moreover from II III have "(\<one>\<ra>\<one>) \<cdot>?E \<lsq> f`(\<one>\<cdot>M)"
      using PositiveSet_def Int_ZF_1_1_L4 by simp
    moreover have "\<forall>k. 
      \<one>\<lsq>k \<and> (k\<ra>\<one>)\<cdot>?E \<lsq> f`(k\<cdot>M) \<longrightarrow> (k\<ra>\<one>\<ra>\<one>)\<cdot>?E \<lsq> f`((k\<ra>\<one>)\<cdot>M)"
    proof -
      { fix k assume A5: "\<one>\<lsq>k"  and A6: "(k\<ra>\<one>)\<cdot>?E \<lsq> f`(k\<cdot>M)"
	with A1 A2 II have T:
	  "k\<in>\<int>"  "M\<in>\<int>"  "k\<ra>\<one> \<in> \<int>"  "?E\<in>\<int>"  "(k\<ra>\<one>)\<cdot>?E \<in> \<int>"  "\<two>\<cdot>?E \<in> \<int>"
	  using Int_ZF_2_L1A PositiveSet_def int_zero_one_are_int 
	    Int_ZF_1_1_L5 Int_ZF_2_1_L8 by auto
	from A1 A2 A5 II have 
	  "\<delta>(f,k\<cdot>M,M) \<in> \<int>"   "abs(\<delta>(f,k\<cdot>M,M)) \<lsq> max\<delta>(f)"   "\<zero>\<lsq>D"
	  using Int_ZF_2_L1A PositiveSet_def Int_ZF_1_1_L5 
	    Int_ZF_2_1_L7 Int_ZF_2_L16C by auto
	with III A6 have 
	  "(k\<ra>\<one>)\<cdot>?E \<ra> (\<two>\<cdot>?E \<rs> ?E) \<lsq> f`(k\<cdot>M) \<ra> (f`(M) \<ra> \<delta>(f,k\<cdot>M,M))"
	  using Int_ZF_1_3_L19A int_ineq_add_sides by simp
	with A1 T have "(k\<ra>\<one>\<ra>\<one>)\<cdot>?E \<lsq> f`((k\<ra>\<one>)\<cdot>M)"
	  using Int_ZF_1_1_L1 int_zero_one_are_int Int_ZF_1_1_L4 
	    Int_ZF_1_2_L11 Int_ZF_2_1_L13 by simp
      } then show ?thesis by simp
    qed
    ultimately have "(m\<ra>\<one>)\<cdot>?E \<lsq> f`(m\<cdot>M)" by (rule Induction_on_int)
    with A4 I have "(m\<ra>\<one>)\<cdot>D \<lsq> f`(m\<cdot>M)" using Int_ZF_1_3_L13A
      by simp
  } then have "\<forall>m\<in>\<int>\<^sub>+.(m\<ra>\<one>)\<cdot>D \<lsq> f`(m\<cdot>M)" by simp
  with II show ?thesis by auto
qed

text\<open>A special case of \<open> Arthan_Lem_3\<close> when $D=1$.\<close>

corollary (in int1) Arthan_L_3_spec: assumes A1: "f \<in> \<S>\<^sub>+"
  shows "\<exists>M\<in>\<int>\<^sub>+.\<forall>n\<in>\<int>\<^sub>+. n\<ra>\<one> \<lsq> f`(n\<cdot>M)"
proof -
  have "\<forall>n\<in>\<int>\<^sub>+. n\<ra>\<one> \<in> \<int>"
    using PositiveSet_def int_zero_one_are_int Int_ZF_1_1_L5
    by simp
  then have "\<forall>n\<in>\<int>\<^sub>+. (n\<ra>\<one>)\<cdot>\<one> = n\<ra>\<one>"
    using Int_ZF_1_1_L4 by simp
  moreover from A1 have "\<exists>M\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. (n\<ra>\<one>)\<cdot>\<one> \<lsq> f`(n\<cdot>M)" 
    using int_one_two_are_pos Arthan_Lem_3 by simp
  ultimately show ?thesis by simp
qed

text\<open>We know  from \<open>Group_ZF_3.thy\<close> that finite range functions are almost homomorphisms. 
  Besides reminding that fact for slopes the next lemma shows 
  that finite range functions do not belong to \<open>\<S>\<^sub>+\<close>. 
  This is important, because the projection
  of the set of finite range functions defines zero in the real number construction in \<open>Real_ZF_x.thy\<close> 
  series, while the projection of \<open>\<S>\<^sub>+\<close> becomes the set of (strictly) positive reals. 
  We don't want zero to be positive, do we? The next lemma is a part of Lemma 5 in the Arthan's paper 
  \cite{Arthan2004}.\<close>

lemma (in int1) Int_ZF_2_3_L1B: 
  assumes A1: "f \<in> FinRangeFunctions(\<int>,\<int>)"
  shows "f\<in>\<S>"   "f \<notin> \<S>\<^sub>+"
proof -
  from A1 show "f\<in>\<S>" using Int_ZF_2_1_L1 group1.Group_ZF_3_3_L1
    by auto
  have "\<int>\<^sub>+ \<subseteq> \<int>" using PositiveSet_def by auto
  with A1 have "f``(\<int>\<^sub>+) \<in> Fin(\<int>)"
    using Finite1_L21 by simp
  then have "f``(\<int>\<^sub>+) \<inter> \<int>\<^sub>+ \<in> Fin(\<int>)"
    using Fin_subset_lemma by blast
  thus "f \<notin> \<S>\<^sub>+" by auto
qed

text\<open>We want to show that if $f$ is a slope and neither $f$ nor $-f$ are in \<open>\<S>\<^sub>+\<close>, 
  then $f$ is bounded. The next lemma is the first step towards that goal and 
  shows that if slope is not in \<open>\<S>\<^sub>+\<close> then $f($\<open>\<int>\<^sub>+\<close>$)$ is bounded above.\<close>

lemma (in int1) Int_ZF_2_3_L2: assumes A1: "f\<in>\<S>" and A2: "f \<notin> \<S>\<^sub>+"
  shows "IsBoundedAbove(f``(\<int>\<^sub>+), IntegerOrder)"
proof -
  from A1 have "f:\<int>\<rightarrow>\<int>" using AlmostHoms_def by simp
  then have "f``(\<int>\<^sub>+) \<subseteq> \<int>" using func1_1_L6 by simp
  moreover from A1 A2 have "f``(\<int>\<^sub>+) \<inter> \<int>\<^sub>+ \<in> Fin(\<int>)" by auto
  ultimately show ?thesis using Int_ZF_2_T1 group3.OrderedGroup_ZF_2_L4
    by simp
qed

text\<open>If $f$ is a slope and $-f\notin$ \<open>\<S>\<^sub>+\<close>, then 
  $f($\<open>\<int>\<^sub>+\<close>$)$ is bounded below.\<close>

lemma (in int1) Int_ZF_2_3_L3: assumes A1: "f\<in>\<S>" and A2: "\<fm>f \<notin> \<S>\<^sub>+"
  shows "IsBoundedBelow(f``(\<int>\<^sub>+), IntegerOrder)"
proof -
  from A1 have T: "f:\<int>\<rightarrow>\<int>" using AlmostHoms_def by simp
  then have "(\<sm>(f``(\<int>\<^sub>+))) = (\<fm>f)``(\<int>\<^sub>+)"
    using Int_ZF_1_T2 group0_2_T2 PositiveSet_def func1_1_L15C
    by auto
  with A1 A2 T show "IsBoundedBelow(f``(\<int>\<^sub>+), IntegerOrder)"
    using Int_ZF_2_1_L12 Int_ZF_2_3_L2 PositiveSet_def func1_1_L6 
      Int_ZF_2_T1 group3.OrderedGroup_ZF_2_L5 by simp
qed

text\<open>A slope that is bounded on \<open>\<int>\<^sub>+\<close> is bounded everywhere.\<close>

lemma (in int1) Int_ZF_2_3_L4: 
  assumes A1: "f\<in>\<S>" and A2: "m\<in>\<int>" 
  and A3: "\<forall>n\<in>\<int>\<^sub>+. abs(f`(n)) \<lsq> L"
  shows "abs(f`(m)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> L"
proof -
  from A1 A3 have 
    "\<zero> \<lsq> abs(f`(\<one>))"  "abs(f`(\<one>)) \<lsq> L"
    using int_zero_one_are_int Int_ZF_2_1_L2B int_abs_nonneg int_one_two_are_pos
    by auto
  then have II: "\<zero>\<lsq>L" by (rule Int_order_transitive)
  note A2
  moreover have "abs(f`(\<zero>)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> L"
  proof -
    from A1 have 
      "abs(f`(\<zero>)) \<lsq> max\<delta>(f)"  "\<zero> \<lsq> max\<delta>(f)" 
      and T: "max\<delta>(f) \<in> \<int>"
      using Int_ZF_2_1_L8 by auto
    with II have "abs(f`(\<zero>)) \<lsq> max\<delta>(f) \<ra> max\<delta>(f) \<ra> L"
      using Int_ZF_2_L15F by simp
    with T show ?thesis using Int_ZF_1_1_L4 by simp
  qed
  moreover from A1 A3 II have 
    "\<forall>n\<in>\<int>\<^sub>+. abs(f`(n)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> L"
    using Int_ZF_2_1_L8 Int_ZF_1_3_L5A Int_ZF_2_L15F 
    by simp
  moreover have "\<forall>n\<in>\<int>\<^sub>+. abs(f`(\<rm>n)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> L"
  proof
    fix n assume "n\<in>\<int>\<^sub>+"
    with A1 A3 have
      "\<two>\<cdot>max\<delta>(f) \<in> \<int>"
      "abs(f`(\<rm>n)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> abs(f`(n))"
      "abs(f`(n)) \<lsq> L"
      using int_two_three_are_int Int_ZF_2_1_L8 Int_ZF_1_1_L5
	PositiveSet_def Int_ZF_2_1_L14 by auto
    then show "abs(f`(\<rm>n)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> L"
      using Int_ZF_2_L15A by blast
  qed    
  ultimately show ?thesis by (rule Int_ZF_2_L19B)
qed

text\<open>A slope whose image of the set of positive integers is bounded
  is a finite range function.\<close>

lemma (in int1) Int_ZF_2_3_L4A: 
  assumes A1: "f\<in>\<S>" and A2: "IsBounded(f``(\<int>\<^sub>+), IntegerOrder)"
  shows "f \<in> FinRangeFunctions(\<int>,\<int>)"
proof -
  have T1: "\<int>\<^sub>+ \<subseteq> \<int>" using PositiveSet_def by auto
  from A1 have T2: "f:\<int>\<rightarrow>\<int>" using AlmostHoms_def by simp
  from A2 obtain L where "\<forall>a\<in>f``(\<int>\<^sub>+). abs(a) \<lsq> L"
    using Int_ZF_1_3_L20A by auto
  with T2 T1 have "\<forall>n\<in>\<int>\<^sub>+. abs(f`(n)) \<lsq> L"
    by (rule func1_1_L15B)
  with A1 have "\<forall>m\<in>\<int>. abs(f`(m)) \<lsq> \<two>\<cdot>max\<delta>(f) \<ra> L"
    using Int_ZF_2_3_L4 by simp
  with T2 have "f``(\<int>) \<in> Fin(\<int>)"
    by (rule Int_ZF_1_3_L20C)
  with T2 show "f \<in> FinRangeFunctions(\<int>,\<int>)"
    using FinRangeFunctions_def by simp
qed

text\<open>A slope whose image of the set of positive integers is bounded
  below is a finite range function or a positive slope.\<close>

lemma (in int1) Int_ZF_2_3_L4B: 
  assumes "f\<in>\<S>" and "IsBoundedBelow(f``(\<int>\<^sub>+), IntegerOrder)"
  shows "f \<in> FinRangeFunctions(\<int>,\<int>) \<or> f\<in>\<S>\<^sub>+"
  using assms Int_ZF_2_3_L2 IsBounded_def Int_ZF_2_3_L4A
  by auto

text\<open>If one slope is not greater then another on positive integers,
  then they are almost equal or the difference is a positive slope.\<close>

lemma (in int1) Int_ZF_2_3_L4C: assumes A1: "f\<in>\<S>"  "g\<in>\<S>" and
  A2: "\<forall>n\<in>\<int>\<^sub>+. f`(n) \<lsq> g`(n)"
  shows "f\<sim>g \<or> g \<fp> (\<fm>f) \<in> \<S>\<^sub>+"
proof -
  let ?h = "g \<fp> (\<fm>f)"
  from A1 have "(\<fm>f) \<in> \<S>" using Int_ZF_2_1_L12 
    by simp
  with A1 have I: "?h \<in> \<S>" using Int_ZF_2_1_L12C 
    by simp
  moreover have "IsBoundedBelow(?h``(\<int>\<^sub>+), IntegerOrder)"
  proof -
    from I have 
      "?h:\<int>\<rightarrow>\<int>" and "\<int>\<^sub>+\<subseteq>\<int>" using AlmostHoms_def PositiveSet_def
      by auto
    moreover from A1 A2 have "\<forall>n\<in>\<int>\<^sub>+. \<langle>\<zero>, ?h`(n)\<rangle> \<in> IntegerOrder"
      using Int_ZF_2_1_L2B PositiveSet_def Int_ZF_1_3_L10A 
	Int_ZF_2_1_L12 Int_ZF_2_1_L12B Int_ZF_2_1_L12A
      by simp
    ultimately show "IsBoundedBelow(?h``(\<int>\<^sub>+), IntegerOrder)"
      by (rule func_ZF_8_L1)
  qed
  ultimately have "?h \<in> FinRangeFunctions(\<int>,\<int>) \<or> ?h\<in>\<S>\<^sub>+"
    using Int_ZF_2_3_L4B by simp
  with A1 show "f\<sim>g \<or> g \<fp> (\<fm>f) \<in> \<S>\<^sub>+"
    using Int_ZF_2_1_L9C by auto
qed
  
text\<open>Positive slopes are arbitrarily large for large enough arguments.\<close>

lemma (in int1) Int_ZF_2_3_L5: 
  assumes A1: "f\<in>\<S>\<^sub>+" and A2: "K\<in>\<int>"
  shows "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
proof -
  from A1 obtain M where I: "M\<in>\<int>\<^sub>+" and II: "\<forall>n\<in>\<int>\<^sub>+. n\<ra>\<one> \<lsq> f`(n\<cdot>M)"
    using Arthan_L_3_spec by auto
  let ?j = "GreaterOf(IntegerOrder,M,K \<rs> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f)) \<rs> \<one>)"
  from A1 I have T1: 
    "minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f) \<in> \<int>"  "M\<in>\<int>"
    using Int_ZF_2_1_L15 Int_ZF_2_1_L8 Int_ZF_1_1_L5 PositiveSet_def
    by auto
  with A2 I have T2: 
    "K \<rs> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f)) \<in> \<int>"
    "K \<rs> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f)) \<rs> \<one> \<in> \<int>"
    using Int_ZF_1_1_L5 int_zero_one_are_int by auto
  with T1 have III: "M \<lsq> ?j"  and 
    "K \<rs> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f)) \<rs> \<one> \<lsq> ?j"
    using Int_ZF_1_3_L18 by auto
  with A2 T1 T2 have 
    IV: "K \<lsq> ?j\<ra>\<one> \<ra> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f))"
    using int_zero_one_are_int Int_ZF_2_L9C by simp
  let ?N = "GreaterOf(IntegerOrder,\<one>,?j\<cdot>M)"
  from T1 III have T3: "?j \<in> \<int>"  "?j\<cdot>M \<in> \<int>"
    using Int_ZF_2_L1A Int_ZF_1_1_L5 by auto
  then have V: "?N \<in> \<int>\<^sub>+" and VI: "?j\<cdot>M \<lsq> ?N"
    using int_zero_one_are_int Int_ZF_1_5_L3 Int_ZF_1_3_L18 
    by auto
  { fix m
    let ?n = "m zdiv M"
    let ?k = "m zmod M"
    assume "?N\<lsq>m"
    with VI have "?j\<cdot>M \<lsq> m" by (rule Int_order_transitive)
    with I III have 
      VII: "m = ?n\<cdot>M\<ra>?k" 
      "?j \<lsq> ?n"  and 
      VIII: "?n \<in> \<int>\<^sub>+"  "?k \<in> \<zero>..(M\<rs>\<one>)"
      using IntDiv_ZF_1_L5 by auto
    with II have 
      "?j \<ra> \<one> \<lsq> ?n \<ra> \<one>"  "?n\<ra>\<one> \<lsq> f`(?n\<cdot>M)"
      using int_zero_one_are_int int_ord_transl_inv by auto
    then have "?j \<ra> \<one> \<lsq>  f`(?n\<cdot>M)"
      by (rule Int_order_transitive)
    with T1 have 
      "?j\<ra>\<one> \<ra> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f)) \<lsq>  
      f`(?n\<cdot>M) \<ra> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f))"
      using int_ord_transl_inv by simp
    with IV have "K \<lsq> f`(?n\<cdot>M) \<ra> (minf(f,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(f))"
      by (rule Int_order_transitive)
    moreover from A1 I VIII have
      "f`(?n\<cdot>M) \<ra> (minf(f,\<zero>..(M\<rs>\<one>))\<rs> max\<delta>(f)) \<lsq> f`(?n\<cdot>M\<ra>?k)"
      using PositiveSet_def Int_ZF_2_1_L16 by simp
    ultimately have "K \<lsq> f`(?n\<cdot>M\<ra>?k)"
      by (rule Int_order_transitive)
    with VII have "K \<lsq> f`(m)" by simp
    } then have  "\<forall>m. ?N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
      by simp
    with V show ?thesis by auto
qed

text\<open>Positive slopes are arbitrarily small for small enough arguments.
  Kind of dual to \<open>Int_ZF_2_3_L5\<close>.\<close>

lemma (in int1) Int_ZF_2_3_L5A: assumes A1: "f\<in>\<S>\<^sub>+" and A2: "K\<in>\<int>"
  shows "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> f`(\<rm>m) \<lsq> K"
proof -
  from A1 have T1: "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<in> \<int>"
    using Int_ZF_2_1_L8 by auto
  with A2 have "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<in> \<int>"
    using Int_ZF_1_1_L5 by simp
  with A1 have 
    "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<lsq> f`(m)"
    using Int_ZF_2_3_L5 by simp
  then obtain N where I: "N\<in>\<int>\<^sub>+" and II:
    "\<forall>m. N\<lsq>m \<longrightarrow>  abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<lsq> f`(m)"
    by auto
  { fix m assume A3: "N\<lsq>m"
    with A1 have
      "f`(\<rm>m) \<lsq> abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> f`(m)"
      using Int_ZF_2_L1A Int_ZF_2_1_L14 by simp
    moreover
    from II T1 A3 have "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> f`(m) \<lsq> 
      (abs(f`(\<zero>)) \<ra> max\<delta>(f)) \<rs>(abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K)"
      using Int_ZF_2_L10 int_ord_transl_inv by simp
    with A2 T1 have "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> f`(m) \<lsq> K"
      using Int_ZF_1_2_L3 by simp
    ultimately have "f`(\<rm>m) \<lsq> K"
      by (rule Int_order_transitive)
  } then have "\<forall>m. N\<lsq>m  \<longrightarrow> f`(\<rm>m) \<lsq> K"
    by simp
  with I show ?thesis by auto
qed

(*lemma (in int1) Int_ZF_2_3_L5A: assumes A1: "f\<in>\<S>\<^sub>+" and A2: "K\<in>\<int>"
  shows "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. m\<lsq>(\<rm>N) \<longrightarrow> f`(m) \<lsq> K"
proof -
  from A1 have T1: "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<in> \<int>"
    using Int_ZF_2_1_L8 by auto;
  with A2 have "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<in> \<int>"
    using Int_ZF_1_1_L5 by simp;
  with A1 have 
    "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<lsq> f`(m)"
    using Int_ZF_2_3_L5 by simp;
  then obtain N where I: "N\<in>\<int>\<^sub>+" and II:
    "\<forall>m. N\<lsq>m \<longrightarrow>  abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<lsq> f`(m)"
    by auto;
  { fix m assume A3: "m\<lsq>(\<rm>N)"
    with A1 have T2: "f`(m) \<in> \<int>"
      using Int_ZF_2_L1A Int_ZF_2_1_L2B by simp;
    from A1 I II A3 have
      "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<lsq> f`(\<rm>m)" and
      "f`(\<rm>m) \<lsq> abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> f`(m)"
       using PositiveSet_def Int_ZF_2_L10AA Int_ZF_2_L1A Int_ZF_2_1_L14
       by auto;
    then have 
      "abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> K \<lsq> abs(f`(\<zero>)) \<ra> max\<delta>(f) \<rs> f`(m)"
      by (rule Int_order_transitive)
    with T1 A2 T2 have "f`(m) \<lsq> K"
      using Int_ZF_2_L10AB by simp; 
  } then have "\<forall>m. m\<lsq>(\<rm>N) \<longrightarrow> f`(m) \<lsq> K"
    by simp;
  with I show ?thesis by auto;
qed;*)

text\<open>A special case of \<open>Int_ZF_2_3_L5\<close> where $K=1$.\<close>

corollary (in int1) Int_ZF_2_3_L6: assumes "f\<in>\<S>\<^sub>+"
  shows "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> f`(m) \<in> \<int>\<^sub>+"
  using assms int_zero_one_are_int Int_ZF_2_3_L5 Int_ZF_1_5_L3
  by simp

text\<open>A special case of \<open>Int_ZF_2_3_L5\<close> where $m=N$.\<close> 

corollary (in int1) Int_ZF_2_3_L6A: assumes "f\<in>\<S>\<^sub>+" and "K\<in>\<int>"
   shows "\<exists>N\<in>\<int>\<^sub>+. K \<lsq> f`(N)"
proof -
  from assms have "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
    using Int_ZF_2_3_L5 by simp
  then obtain N where I: "N \<in> \<int>\<^sub>+"  and II: "\<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
    by auto
  then show ?thesis using PositiveSet_def int_ord_is_refl refl_def
    by auto
qed

text\<open>If values of a slope are not bounded above, 
  then the slope is positive.\<close>

lemma (in int1) Int_ZF_2_3_L7: assumes A1: "f\<in>\<S>" 
  and A2: "\<forall>K\<in>\<int>. \<exists>n\<in>\<int>\<^sub>+. K \<lsq> f`(n)"
  shows "f \<in> \<S>\<^sub>+"
proof -
  { fix K assume "K\<in>\<int>"
    with A2 obtain n where "n\<in>\<int>\<^sub>+"  "K \<lsq> f`(n)"
      by auto
    moreover from A1 have "\<int>\<^sub>+ \<subseteq> \<int>"  "f:\<int>\<rightarrow>\<int>" 
      using PositiveSet_def AlmostHoms_def by auto
    ultimately have "\<exists>m \<in> f``(\<int>\<^sub>+). K \<lsq> m" 
      using func1_1_L15D by auto
  } then have "\<forall>K\<in>\<int>. \<exists>m \<in> f``(\<int>\<^sub>+). K \<lsq> m" by simp
  with A1 show "f \<in> \<S>\<^sub>+" using Int_ZF_4_L9 Int_ZF_2_3_L2
    by auto
qed

text\<open>For unbounded slope $f$ either $f\in$\<open>\<S>\<^sub>+\<close> of 
  $-f\in$\<open>\<S>\<^sub>+\<close>.\<close>

theorem (in int1) Int_ZF_2_3_L8:
  assumes A1: "f\<in>\<S>" and A2: "f \<notin> FinRangeFunctions(\<int>,\<int>)"
  shows "(f \<in> \<S>\<^sub>+) Xor ((\<fm>f) \<in> \<S>\<^sub>+)"
proof -
  have T1: "\<int>\<^sub>+ \<subseteq> \<int>" using PositiveSet_def by auto
  from A1 have T2: "f:\<int>\<rightarrow>\<int>"  using AlmostHoms_def by simp
  then have I: "f``(\<int>\<^sub>+) \<subseteq> \<int>" using func1_1_L6 by auto
  from A1 A2 have "f \<in> \<S>\<^sub>+ \<or> (\<fm>f) \<in> \<S>\<^sub>+"
    using Int_ZF_2_3_L2 Int_ZF_2_3_L3 IsBounded_def Int_ZF_2_3_L4A
    by blast
  moreover have "\<not>(f \<in> \<S>\<^sub>+ \<and> (\<fm>f) \<in> \<S>\<^sub>+)"
  proof -
    { assume A3: "f \<in> \<S>\<^sub>+"  and A4: "(\<fm>f) \<in> \<S>\<^sub>+"
      from A3 obtain N1 where 
	I: "N1\<in>\<int>\<^sub>+" and II: "\<forall>m. N1\<lsq>m \<longrightarrow> f`(m) \<in> \<int>\<^sub>+"
	using Int_ZF_2_3_L6 by auto
      from A4 obtain N2 where 
	III: "N2\<in>\<int>\<^sub>+" and IV: "\<forall>m. N2\<lsq>m \<longrightarrow> (\<fm>f)`(m) \<in> \<int>\<^sub>+"
	using Int_ZF_2_3_L6 by auto
      let ?N = "GreaterOf(IntegerOrder,N1,N2)"
      from I III have "N1 \<lsq> ?N"  "N2 \<lsq> ?N"
	using PositiveSet_def Int_ZF_1_3_L18 by auto
      with A1 II IV have
	"f`(?N) \<in> \<int>\<^sub>+"  "(\<fm>f)`(?N) \<in> \<int>\<^sub>+"  "(\<fm>f)`(?N) = \<rm>(f`(?N))"
	using Int_ZF_2_L1A PositiveSet_def Int_ZF_2_1_L12A
	by auto
      then have False using Int_ZF_1_5_L8 by simp
    } thus ?thesis by auto
  qed
  ultimately show "(f \<in> \<S>\<^sub>+) Xor ((\<fm>f) \<in> \<S>\<^sub>+)"
    using Xor_def by simp
qed

text\<open>The sum of positive slopes is a positive slope.\<close>

theorem (in int1) sum_of_pos_sls_is_pos_sl: 
  assumes A1: "f \<in> \<S>\<^sub>+"  "g \<in> \<S>\<^sub>+"
  shows "f\<fp>g \<in> \<S>\<^sub>+"
proof -
  { fix K assume "K\<in>\<int>"
    with A1 have "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
      using Int_ZF_2_3_L5 by simp
    then obtain N where I: "N\<in>\<int>\<^sub>+" and II: "\<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
      by auto
    from A1 have "\<exists>M\<in>\<int>\<^sub>+. \<forall>m. M\<lsq>m \<longrightarrow> \<zero> \<lsq> g`(m)"
      using int_zero_one_are_int Int_ZF_2_3_L5 by simp
    then obtain M where III: "M\<in>\<int>\<^sub>+" and IV: "\<forall>m. M\<lsq>m \<longrightarrow> \<zero> \<lsq> g`(m)"
      by auto
    let ?L = "GreaterOf(IntegerOrder,N,M)"
    from I III have V: "?L \<in> \<int>\<^sub>+"  "\<int>\<^sub>+ \<subseteq> \<int>" 
      using GreaterOf_def PositiveSet_def by auto
    moreover from A1 V have "(f\<fp>g)`(?L) = f`(?L) \<ra> g`(?L)"
      using Int_ZF_2_1_L12B by auto
    moreover from I II III IV have "K \<lsq> f`(?L) \<ra> g`(?L)"
      using PositiveSet_def Int_ZF_1_3_L18 Int_ZF_2_L15F
      by simp
    ultimately have "?L \<in> \<int>\<^sub>+"  "K \<lsq> (f\<fp>g)`(?L)"
      by auto
    then have "\<exists>n \<in>\<int>\<^sub>+. K \<lsq> (f\<fp>g)`(n)"
      by auto
  } with A1 show "f\<fp>g \<in> \<S>\<^sub>+"
    using Int_ZF_2_1_L12C Int_ZF_2_3_L7 by simp
qed

text\<open>The composition of positive slopes is a positive slope.\<close>

theorem (in int1) comp_of_pos_sls_is_pos_sl: 
  assumes A1: "f \<in> \<S>\<^sub>+"  "g \<in> \<S>\<^sub>+"
  shows "f\<circ>g \<in> \<S>\<^sub>+"
proof -
  { fix K assume "K\<in>\<int>"
    with A1 have "\<exists>N\<in>\<int>\<^sub>+. \<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
      using Int_ZF_2_3_L5 by simp
    then obtain N where "N\<in>\<int>\<^sub>+" and I: "\<forall>m. N\<lsq>m \<longrightarrow> K \<lsq> f`(m)"
      by auto
    with A1 have "\<exists>M\<in>\<int>\<^sub>+. N \<lsq> g`(M)"
      using PositiveSet_def Int_ZF_2_3_L6A by simp
    then obtain M where "M\<in>\<int>\<^sub>+"  "N \<lsq> g`(M)"
      by auto
    with A1 I have "\<exists>M\<in>\<int>\<^sub>+. K \<lsq> (f\<circ>g)`(M)"
      using PositiveSet_def Int_ZF_2_1_L10
      by auto
  } with A1 show "f\<circ>g \<in> \<S>\<^sub>+"
    using Int_ZF_2_1_L11 Int_ZF_2_3_L7
    by simp
qed

text\<open>A slope equivalent to a positive one is positive.\<close>

lemma (in int1) Int_ZF_2_3_L9: 
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "\<langle>f,g\<rangle> \<in> AlEqRel" shows "g \<in> \<S>\<^sub>+"
proof -
  from A2 have T: "g\<in>\<S>" and "\<exists>L\<in>\<int>. \<forall>m\<in>\<int>. abs(f`(m)\<rs>g`(m)) \<lsq> L"
    using Int_ZF_2_1_L9A by auto
   then obtain L where 
     I: "L\<in>\<int>"  and II: "\<forall>m\<in>\<int>. abs(f`(m)\<rs>g`(m)) \<lsq> L"
     by auto
  { fix K assume A3: "K\<in>\<int>"
    with I have "K\<ra>L \<in> \<int>"
      using Int_ZF_1_1_L5 by simp
    with A1 obtain M where III: "M\<in>\<int>\<^sub>+"  and IV: "K\<ra>L \<lsq> f`(M)"
      using Int_ZF_2_3_L6A by auto
    with A1 A3 I have  "K \<lsq> f`(M)\<rs>L"
      using PositiveSet_def Int_ZF_2_1_L2B Int_ZF_2_L9B
      by simp
    moreover from A1 T II III have  
      "f`(M)\<rs>L \<lsq> g`(M)"
      using PositiveSet_def Int_ZF_2_1_L2B Int_triangle_ineq2
      by simp
    ultimately have "K \<lsq>  g`(M)"
      by (rule Int_order_transitive)
    with III have "\<exists>n\<in>\<int>\<^sub>+. K \<lsq> g`(n)"
      by auto
  } with T show "g \<in> \<S>\<^sub>+"
    using Int_ZF_2_3_L7 by simp
qed

text\<open>The set of positive slopes is saturated with respect to the relation of 
  equivalence of slopes.\<close>

lemma (in int1) pos_slopes_saturated: shows "IsSaturated(AlEqRel,\<S>\<^sub>+)"
proof -
  have 
    "equiv(\<S>,AlEqRel)" 
    "AlEqRel \<subseteq> \<S> \<times> \<S>"
    using Int_ZF_2_1_L9B by auto
  moreover have "\<S>\<^sub>+ \<subseteq> \<S>" by auto
  moreover have "\<forall>f\<in>\<S>\<^sub>+. \<forall>g\<in>\<S>. \<langle>f,g\<rangle> \<in> AlEqRel \<longrightarrow> g \<in> \<S>\<^sub>+"
    using Int_ZF_2_3_L9 by blast
  ultimately show "IsSaturated(AlEqRel,\<S>\<^sub>+)"
    by (rule EquivClass_3_L3)
qed
  
text\<open>A technical lemma involving a projection of the set of positive slopes
  and a logical epression with exclusive or.\<close>

lemma (in int1) Int_ZF_2_3_L10:
  assumes A1: "f\<in>\<S>"  "g\<in>\<S>"
  and A2: "R = {AlEqRel``{s}. s\<in>\<S>\<^sub>+}"
  and A3: "(f\<in>\<S>\<^sub>+) Xor (g\<in>\<S>\<^sub>+)"
  shows "(AlEqRel``{f} \<in> R) Xor (AlEqRel``{g} \<in> R)"
proof -
  from A1 A2 A3 have 
    "equiv(\<S>,AlEqRel)" 
    "IsSaturated(AlEqRel,\<S>\<^sub>+)"
    "\<S>\<^sub>+ \<subseteq> \<S>"
    "f\<in>\<S>"  "g\<in>\<S>"
    "R = {AlEqRel``{s}. s\<in>\<S>\<^sub>+}"
    "(f\<in>\<S>\<^sub>+) Xor (g\<in>\<S>\<^sub>+)"
    using pos_slopes_saturated Int_ZF_2_1_L9B by auto
  then show ?thesis by (rule EquivClass_3_L7)
qed

text\<open>Identity function is a positive slope.\<close>

lemma (in int1) Int_ZF_2_3_L11: shows "id(\<int>) \<in> \<S>\<^sub>+"
proof -
  let ?f = "id(\<int>)"
  { fix K assume "K\<in>\<int>" 
    then obtain n where T: "n\<in>\<int>\<^sub>+" and "K\<lsq>n"
      using Int_ZF_1_5_L9 by auto
    moreover from T have "?f`(n) = n"
      using PositiveSet_def by simp
    ultimately have  "n\<in>\<int>\<^sub>+" and "K\<lsq>?f`(n)"
      by auto
    then have "\<exists>n\<in>\<int>\<^sub>+. K\<lsq>?f`(n)" by auto
  } then show "?f \<in> \<S>\<^sub>+"
    using Int_ZF_2_1_L17 Int_ZF_2_3_L7 by simp
qed
      
text\<open>The identity function is not almost equal to any bounded function.\<close>

lemma (in int1) Int_ZF_2_3_L12: assumes A1: "f \<in> FinRangeFunctions(\<int>,\<int>)"
  shows "\<not>(id(\<int>) \<sim> f)"
proof -
  { from A1 have "id(\<int>) \<in> \<S>\<^sub>+"
      using Int_ZF_2_3_L11 by simp
    moreover assume "\<langle>id(\<int>),f\<rangle> \<in> AlEqRel"
    ultimately have  "f \<in> \<S>\<^sub>+"
      by (rule Int_ZF_2_3_L9)
    with A1 have False using Int_ZF_2_3_L1B
      by simp
  } then show "\<not>(id(\<int>) \<sim> f)" by auto
qed

subsection\<open>Inverting slopes\<close>

text\<open>Not every slope is a 1:1 function. However, we can still invert slopes 
  in the sense that if $f$ is a slope, then we can find a slope $g$ such that
  $f\circ g$  is almost equal to the identity function. 
  The goal of this this section is to establish this fact for positive slopes.
\<close>

text\<open>If $f$ is a positive slope, then for every positive integer $p$ 
  the set $\{n\in Z_+: p\leq f(n)\}$ is a nonempty subset of positive integers.
  Recall that $f^{-1}(p)$ is the notation for the smallest element of this set.\<close>

lemma (in int1) Int_ZF_2_4_L1: 
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "p\<in>\<int>\<^sub>+" and A3: "A = {n\<in>\<int>\<^sub>+. p \<lsq> f`(n)}"
  shows 
  "A \<subseteq> \<int>\<^sub>+"  
  "A \<noteq> 0"
  "f\<inverse>(p) \<in> A"
  "\<forall>m\<in>A. f\<inverse>(p) \<lsq> m"
proof -
  from A3 show I: "A \<subseteq> \<int>\<^sub>+" by auto
  from A1 A2 have "\<exists>n\<in>\<int>\<^sub>+. p \<lsq> f`(n)"
    using PositiveSet_def Int_ZF_2_3_L6A by simp
  with A3 show II: "A \<noteq> 0" by auto
  from A3 I II show 
    "f\<inverse>(p) \<in> A"
    "\<forall>m\<in>A. f\<inverse>(p) \<lsq> m"
    using Int_ZF_1_5_L1C by auto
qed

text\<open>If $f$ is a positive slope and $p$ is a positive integer $p$, then 
   $f^{-1}(p)$ (defined as the minimum of the set $\{n\in Z_+: p\leq f(n)\}$ ) 
  is a (well defined) positive integer.\<close>

lemma (in int1) Int_ZF_2_4_L2: 
  assumes "f \<in> \<S>\<^sub>+" and "p\<in>\<int>\<^sub>+"
  shows 
  "f\<inverse>(p) \<in> \<int>\<^sub>+" 
  "p \<lsq> f`(f\<inverse>(p))"
  using assms Int_ZF_2_4_L1 by auto

text\<open>If $f$ is a positive slope and $p$ is a positive integer such 
  that $n\leq f(p)$, then
  $f^{-1}(n) \leq p$.\<close>

lemma (in int1) Int_ZF_2_4_L3: 
  assumes "f \<in> \<S>\<^sub>+" and  "m\<in>\<int>\<^sub>+"  "p\<in>\<int>\<^sub>+" and "m \<lsq> f`(p)"
  shows "f\<inverse>(m) \<lsq> p"
  using assms Int_ZF_2_4_L1 by simp

text\<open>An upper bound $f(f^{-1}(m) -1)$ for positive slopes.\<close>

lemma (in int1) Int_ZF_2_4_L4: 
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "m\<in>\<int>\<^sub>+" and A3: "f\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
  shows "f`(f\<inverse>(m)\<rs>\<one>) \<lsq> m"   "f`(f\<inverse>(m)\<rs>\<one>) \<noteq> m"
proof -
  from A1 A2 have T: "f\<inverse>(m) \<in> \<int>" using Int_ZF_2_4_L2 PositiveSet_def
    by simp
  from A1 A3 have "f:\<int>\<rightarrow>\<int>"  and "f\<inverse>(m)\<rs>\<one> \<in> \<int>"
    using Int_ZF_2_3_L1 PositiveSet_def by auto
  with A1 A2 have T1: "f`(f\<inverse>(m)\<rs>\<one>) \<in> \<int>"  "m\<in>\<int>" 
    using apply_funtype PositiveSet_def by auto
  { assume "m \<lsq> f`(f\<inverse>(m)\<rs>\<one>)"
    with A1 A2 A3 have "f\<inverse>(m) \<lsq> f\<inverse>(m)\<rs>\<one>" 
      by (rule Int_ZF_2_4_L3)
    with T have False using Int_ZF_1_2_L3AA
      by simp
  } then have I: "\<not>(m \<lsq> f`(f\<inverse>(m)\<rs>\<one>))" by auto
  with T1 show "f`(f\<inverse>(m)\<rs>\<one>) \<lsq> m"   
    by (rule Int_ZF_2_L19)
  from T1 I show "f`(f\<inverse>(m)\<rs>\<one>) \<noteq> m"
    by (rule Int_ZF_2_L19)
qed

text\<open>The (candidate for) the inverse of a positive slope is nondecreasing.\<close>

lemma (in int1) Int_ZF_2_4_L5:
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "m\<in>\<int>\<^sub>+" and A3: "m\<lsq>n"
  shows "f\<inverse>(m) \<lsq> f\<inverse>(n)"
proof -
  from A2 A3 have T: "n \<in> \<int>\<^sub>+" using Int_ZF_1_5_L7 by blast
  with A1 have "n \<lsq> f`(f\<inverse>(n))" using Int_ZF_2_4_L2
    by simp
  with A3 have "m \<lsq> f`(f\<inverse>(n))" by (rule Int_order_transitive)
  with A1 A2 T show "f\<inverse>(m) \<lsq> f\<inverse>(n)"
    using Int_ZF_2_4_L2 Int_ZF_2_4_L3 by simp
qed
  
text\<open>If $f^{-1}(m)$ is positive and $n$ is a positive integer, then, 
  then $f^{-1}(m+n)-1$ is positive.\<close>

lemma (in int1) Int_ZF_2_4_L6: 
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "m\<in>\<int>\<^sub>+"  "n\<in>\<int>\<^sub>+" and 
  A3: "f\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
  shows "f\<inverse>(m\<ra>n)\<rs>\<one> \<in> \<int>\<^sub>+"
proof -
  from A1 A2 have "f\<inverse>(m)\<rs>\<one> \<lsq>  f\<inverse>(m\<ra>n) \<rs> \<one>"
     using PositiveSet_def Int_ZF_1_5_L7A Int_ZF_2_4_L2 
       Int_ZF_2_4_L5 int_zero_one_are_int Int_ZF_1_1_L4 
       int_ord_transl_inv by simp
  with A3 show "f\<inverse>(m\<ra>n)\<rs>\<one> \<in> \<int>\<^sub>+" using Int_ZF_1_5_L7
    by blast
qed

text\<open>If $f$ is a slope, then $f(f^{-1}(m+n)-f^{-1}(m) - f^{-1}(n))$ is 
  uniformly bounded above and below. Will it be the messiest IsarMathLib
  proof ever? Only time will tell.\<close>

lemma (in int1) Int_ZF_2_4_L7:  assumes A1: "f \<in> \<S>\<^sub>+" and
  A2: "\<forall>m\<in>\<int>\<^sub>+. f\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
  shows 
  "\<exists>U\<in>\<int>. \<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n)) \<lsq> U"
  "\<exists>N\<in>\<int>. \<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. N \<lsq> f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n))"
proof -
  from A1 have "\<exists>L\<in>\<int>. \<forall>r\<in>\<int>. f`(r) \<lsq> f`(r\<rs>\<one>) \<ra> L"
    using Int_ZF_2_1_L28 by simp
  then obtain L where 
    I: "L\<in>\<int>" and II: "\<forall>r\<in>\<int>. f`(r) \<lsq> f`(r\<rs>\<one>) \<ra> L"
    by auto
  from A1 have 
    "\<exists>M\<in>\<int>. \<forall>r\<in>\<int>.\<forall>p\<in>\<int>.\<forall>q\<in>\<int>. f`(r\<rs>p\<rs>q) \<lsq> f`(r)\<rs>f`(p)\<rs>f`(q)\<ra>M"
    "\<exists>K\<in>\<int>. \<forall>r\<in>\<int>.\<forall>p\<in>\<int>.\<forall>q\<in>\<int>. f`(r)\<rs>f`(p)\<rs>f`(q)\<ra>K \<lsq> f`(r\<rs>p\<rs>q)"
    using Int_ZF_2_1_L30 by auto
  then obtain M K where III: "M\<in>\<int>" and 
    IV: "\<forall>r\<in>\<int>.\<forall>p\<in>\<int>.\<forall>q\<in>\<int>. f`(r\<rs>p\<rs>q) \<lsq> f`(r)\<rs>f`(p)\<rs>f`(q)\<ra>M" 
    and 
    V: "K\<in>\<int>" and VI: "\<forall>r\<in>\<int>.\<forall>p\<in>\<int>.\<forall>q\<in>\<int>. f`(r)\<rs>f`(p)\<rs>f`(q)\<ra>K \<lsq> f`(r\<rs>p\<rs>q)"
    by auto
  from I III V have 
    "L\<ra>M \<in> \<int>"  "(\<rm>L) \<rs> L \<ra> K \<in> \<int>" 
    using Int_ZF_1_1_L4 Int_ZF_1_1_L5 by auto
  moreover
    { fix m n
      assume A3: "m\<in>\<int>\<^sub>+" "n\<in>\<int>\<^sub>+" 
      have  "f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n)) \<lsq>  L\<ra>M \<and> 
	(\<rm>L)\<rs>L\<ra>K \<lsq> f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n))"
      proof -
	let ?r = "f\<inverse>(m\<ra>n)"
	let ?p = "f\<inverse>(m)"
	let ?q = "f\<inverse>(n)"
	from A1 A3 have T1:
	  "?p \<in> \<int>\<^sub>+"  "?q \<in> \<int>\<^sub>+"  "?r \<in> \<int>\<^sub>+"
	  using Int_ZF_2_4_L2 pos_int_closed_add_unfolded by auto
	with A3 have T2:
	  "m \<in> \<int>"  "n \<in> \<int>"  "?p \<in> \<int>"  "?q \<in> \<int>"  "?r \<in> \<int>" 
	  using PositiveSet_def by auto
	from A2 A3 have T3:
	  "?r\<rs>\<one> \<in> \<int>\<^sub>+" "?p\<rs>\<one> \<in> \<int>\<^sub>+"  "?q\<rs>\<one> \<in> \<int>\<^sub>+"
	  using pos_int_closed_add_unfolded by auto
	from A1 A3 have VII:
	  "m\<ra>n \<lsq> f`(?r)"
	  "m \<lsq> f`(?p)"  
	  "n \<lsq> f`(?q)"  
	  using Int_ZF_2_4_L2 pos_int_closed_add_unfolded by auto
	from A1 A3 T3 have VIII:
	  "f`(?r\<rs>\<one>) \<lsq> m\<ra>n"
	  "f`(?p\<rs>\<one>) \<lsq> m"
	  "f`(?q\<rs>\<one>) \<lsq> n"
	  using pos_int_closed_add_unfolded Int_ZF_2_4_L4 by auto
	have "f`(?r\<rs>?p\<rs>?q) \<lsq> L\<ra>M"
	proof -
	  from IV T2 have "f`(?r\<rs>?p\<rs>?q) \<lsq> f`(?r)\<rs>f`(?p)\<rs>f`(?q)\<ra>M"
	    by simp
	  moreover 
	  from I II T2 VIII have
	    "f`(?r) \<lsq> f`(?r\<rs>\<one>) \<ra> L"
	    "f`(?r\<rs>\<one>) \<ra> L \<lsq> m\<ra>n\<ra>L"
	    using int_ord_transl_inv by auto
	  then have "f`(?r) \<lsq>  m\<ra>n\<ra>L"
	    by (rule Int_order_transitive)
	  with VII have "f`(?r) \<rs> f`(?p) \<lsq> m\<ra>n\<ra>L\<rs>m"
	    using int_ineq_add_sides by simp
	  with I T2 VII have "f`(?r) \<rs> f`(?p) \<rs> f`(?q) \<lsq> n\<ra>L\<rs>n"
	    using Int_ZF_1_2_L9 int_ineq_add_sides by simp
	  with I III T2 have "f`(?r) \<rs> f`(?p) \<rs> f`(?q) \<ra> M \<lsq> L\<ra>M"
	    using Int_ZF_1_2_L3 int_ord_transl_inv by simp
	  ultimately show "f`(?r\<rs>?p\<rs>?q) \<lsq> L\<ra>M"
	    by (rule Int_order_transitive)
	qed
	moreover have "(\<rm>L)\<rs>L \<ra>K \<lsq> f`(?r\<rs>?p\<rs>?q)"
	proof -
	  from I II T2 VIII have
	    "f`(?p) \<lsq> f`(?p\<rs>\<one>) \<ra> L"
	    "f`(?p\<rs>\<one>) \<ra> L \<lsq> m \<ra>L"
	    using int_ord_transl_inv by auto
	  then have "f`(?p) \<lsq>  m \<ra>L"
	    by (rule Int_order_transitive)
	  with VII have "m\<ra>n \<rs>(m\<ra>L) \<lsq> f`(?r) \<rs> f`(?p)"
	    using int_ineq_add_sides by simp
	  with I T2 have "n \<rs> L \<lsq>  f`(?r) \<rs> f`(?p)"
	    using Int_ZF_1_2_L9 by simp
	  moreover
	  from I II T2 VIII have
	    "f`(?q) \<lsq> f`(?q\<rs>\<one>) \<ra> L"
	    "f`(?q\<rs>\<one>) \<ra> L \<lsq> n \<ra>L"
	    using int_ord_transl_inv by auto
	  then have "f`(?q) \<lsq>  n \<ra>L"
	    by (rule Int_order_transitive)
	  ultimately have 
	    "n \<rs> L \<rs> (n\<ra>L) \<lsq>  f`(?r) \<rs> f`(?p) \<rs> f`(?q)"
	    using int_ineq_add_sides by simp
	  with I V T2 have 
	    "(\<rm>L)\<rs>L \<ra>K \<lsq>  f`(?r) \<rs> f`(?p) \<rs> f`(?q) \<ra> K"
	    using Int_ZF_1_2_L3 int_ord_transl_inv by simp
	  moreover from VI T2 have
	    "f`(?r) \<rs> f`(?p) \<rs> f`(?q) \<ra> K \<lsq> f`(?r\<rs>?p\<rs>?q)"
	    by simp
	  ultimately show "(\<rm>L)\<rs>L \<ra>K \<lsq> f`(?r\<rs>?p\<rs>?q)"
	    by (rule Int_order_transitive)
	qed
	ultimately show
	  "f`(?r\<rs>?p\<rs>?q) \<lsq>  L\<ra>M \<and> 
	  (\<rm>L)\<rs>L\<ra>K \<lsq> f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n))" 
	  by simp 
      qed 
    }
  ultimately show 
    "\<exists>U\<in>\<int>. \<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n)) \<lsq> U"
    "\<exists>N\<in>\<int>. \<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. N \<lsq> f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n))"
    by auto
qed

text\<open>The expression $f^{-1}(m+n)-f^{-1}(m) - f^{-1}(n)$ is uniformly bounded
  for all pairs $\langle m,n \rangle \in$ \<open>\<int>\<^sub>+\<times>\<int>\<^sub>+\<close>. 
  Recall that in the \<open>int1\<close>
  context \<open>\<epsilon>(f,x)\<close> is defined so that 
  $\varepsilon(f,\langle m,n \rangle ) = f^{-1}(m+n)-f^{-1}(m) - f^{-1}(n)$.\<close>

lemma (in int1) Int_ZF_2_4_L8:  assumes A1: "f \<in> \<S>\<^sub>+" and
  A2: "\<forall>m\<in>\<int>\<^sub>+. f\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
  shows "\<exists>M. \<forall>x\<in>\<int>\<^sub>+\<times>\<int>\<^sub>+. abs(\<epsilon>(f,x)) \<lsq> M"
proof -
  from A1 A2 have 
    "\<exists>U\<in>\<int>. \<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n)) \<lsq> U"
    "\<exists>N\<in>\<int>. \<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. N \<lsq> f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n))"
    using  Int_ZF_2_4_L7 by auto
  then obtain U N where I:
    "\<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n)) \<lsq> U" 
    "\<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. N \<lsq> f`(f\<inverse>(m\<ra>n)\<rs>f\<inverse>(m)\<rs>f\<inverse>(n))"
    by auto
  have "\<int>\<^sub>+\<times>\<int>\<^sub>+ \<noteq> 0" using int_one_two_are_pos by auto
  moreover from A1 have "f: \<int>\<rightarrow>\<int>"
    using AlmostHoms_def by simp
  moreover from A1 have
    "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)"
    using Int_ZF_2_3_L5 by simp
  moreover from A1 have
    "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> f`(\<rm>y) \<lsq> a"
    using Int_ZF_2_3_L5A by simp
  moreover have 
    "\<forall>x\<in>\<int>\<^sub>+\<times>\<int>\<^sub>+. \<epsilon>(f,x) \<in> \<int> \<and> f`(\<epsilon>(f,x)) \<lsq> U \<and> N \<lsq> f`(\<epsilon>(f,x))"
  proof -
    { fix x assume A3: "x \<in> \<int>\<^sub>+\<times>\<int>\<^sub>+"
      let ?m = "fst(x)"
      let ?n = "snd(x)"
      from A3 have T: "?m \<in> \<int>\<^sub>+"  "?n \<in> \<int>\<^sub>+"  "?m\<ra>?n \<in> \<int>\<^sub>+"
	using pos_int_closed_add_unfolded by auto
      with A1 have 
	"f\<inverse>(?m\<ra>?n) \<in> \<int>"  "f\<inverse>(?m) \<in> \<int>"  "f\<inverse>(?n) \<in> \<int>"
	using Int_ZF_2_4_L2 PositiveSet_def by auto
      with I T have 
	"\<epsilon>(f,x) \<in> \<int> \<and> f`(\<epsilon>(f,x)) \<lsq> U \<and> N \<lsq> f`(\<epsilon>(f,x))"
	using Int_ZF_1_1_L5 by auto 
    } thus ?thesis by simp
    qed
  ultimately show "\<exists>M.\<forall>x\<in>\<int>\<^sub>+\<times>\<int>\<^sub>+. abs(\<epsilon>(f,x)) \<lsq> M"
    by (rule Int_ZF_1_6_L4)
qed
  
text\<open>The (candidate for) inverse of a positive slope is a (well defined) 
  function on \<open>\<int>\<^sub>+\<close>.\<close>

lemma (in int1) Int_ZF_2_4_L9: 
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "g = {\<langle>p,f\<inverse>(p)\<rangle>. p\<in>\<int>\<^sub>+}"
  shows 
  "g : \<int>\<^sub>+\<rightarrow>\<int>\<^sub>+"
  "g : \<int>\<^sub>+\<rightarrow>\<int>"
proof -
  from A1 have 
    "\<forall>p\<in>\<int>\<^sub>+. f\<inverse>(p) \<in> \<int>\<^sub>+" 
    "\<forall>p\<in>\<int>\<^sub>+. f\<inverse>(p) \<in> \<int>" 
    using Int_ZF_2_4_L2 PositiveSet_def by auto
  with A2 show 
    "g : \<int>\<^sub>+\<rightarrow>\<int>\<^sub>+"  and  "g : \<int>\<^sub>+\<rightarrow>\<int>" 
    using ZF_fun_from_total by auto
qed

text\<open>What are the values of the (candidate for) the inverse of a positive slope?\<close>

lemma (in int1) Int_ZF_2_4_L10: 
  assumes A1: "f \<in> \<S>\<^sub>+" and A2: "g = {\<langle>p,f\<inverse>(p)\<rangle>. p\<in>\<int>\<^sub>+}" and A3: "p\<in>\<int>\<^sub>+"
  shows "g`(p) = f\<inverse>(p)"
proof -
  from A1 A2 have  "g : \<int>\<^sub>+\<rightarrow>\<int>\<^sub>+" using Int_ZF_2_4_L9 by simp
  with A2 A3 show "g`(p) = f\<inverse>(p)" using ZF_fun_from_tot_val by simp
qed

text\<open>The (candidate for) the inverse of a positive slope is a slope.\<close>

lemma (in int1) Int_ZF_2_4_L11: assumes A1: "f \<in> \<S>\<^sub>+" and 
  A2: "\<forall>m\<in>\<int>\<^sub>+. f\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+" and
  A3: "g = {\<langle>p,f\<inverse>(p)\<rangle>. p\<in>\<int>\<^sub>+}"
  shows "OddExtension(\<int>,IntegerAddition,IntegerOrder,g) \<in> \<S>"
proof -
  from A1 A2 have "\<exists>L. \<forall>x\<in>\<int>\<^sub>+\<times>\<int>\<^sub>+. abs(\<epsilon>(f,x)) \<lsq> L"
    using Int_ZF_2_4_L8 by simp
  then obtain L where I: "\<forall>x\<in>\<int>\<^sub>+\<times>\<int>\<^sub>+. abs(\<epsilon>(f,x)) \<lsq> L"
    by auto
  from A1 A3 have "g : \<int>\<^sub>+\<rightarrow>\<int>" using Int_ZF_2_4_L9 
    by simp
  moreover have "\<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. abs(\<delta>(g,m,n)) \<lsq> L"
  proof-
    { fix m n
      assume A4: "m\<in>\<int>\<^sub>+"  "n\<in>\<int>\<^sub>+"
      then have "\<langle>m,n\<rangle> \<in> \<int>\<^sub>+\<times>\<int>\<^sub>+" by simp
      with I have "abs(\<epsilon>(f,\<langle>m,n\<rangle>)) \<lsq> L" by simp
      moreover have "\<epsilon>(f,\<langle>m,n\<rangle>) = f\<inverse>(m\<ra>n) \<rs> f\<inverse>(m) \<rs> f\<inverse>(n)"
	by simp
      moreover from A1 A3 A4 have
	"f\<inverse>(m\<ra>n) = g`(m\<ra>n)"  "f\<inverse>(m) = g`(m)"  "f\<inverse>(n) = g`(n)"
	using pos_int_closed_add_unfolded Int_ZF_2_4_L10 by auto
      ultimately have "abs(\<delta>(g,m,n)) \<lsq> L" by simp
    } thus "\<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. abs(\<delta>(g,m,n)) \<lsq> L" by simp
  qed
  ultimately show ?thesis by (rule Int_ZF_2_1_L24)
qed
  
text\<open>Every positive slope that is at least $2$ on positive integers
  almost has an inverse.\<close>


lemma (in int1) Int_ZF_2_4_L12: assumes A1: "f \<in> \<S>\<^sub>+" and 
  A2: "\<forall>m\<in>\<int>\<^sub>+. f\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
  shows "\<exists>h\<in>\<S>. f\<circ>h \<sim> id(\<int>)"
proof -
  let ?g = "{\<langle>p,f\<inverse>(p)\<rangle>. p\<in>\<int>\<^sub>+}"
  let ?h = "OddExtension(\<int>,IntegerAddition,IntegerOrder,?g)"
  from A1 have 
    "\<exists>M\<in>\<int>. \<forall>n\<in>\<int>. f`(n) \<lsq> f`(n\<rs>\<one>) \<ra> M"
    using Int_ZF_2_1_L28 by simp
  then obtain M where 
    I: "M\<in>\<int>" and II: "\<forall>n\<in>\<int>. f`(n) \<lsq> f`(n\<rs>\<one>) \<ra> M"
    by auto
  from A1 A2 have T: "?h \<in> \<S>"
    using Int_ZF_2_4_L11 by simp
  moreover have  "f\<circ>?h \<sim> id(\<int>)"
  proof -
    from A1 T have "f\<circ>?h \<in> \<S>" using Int_ZF_2_1_L11 
      by simp
    moreover note I
    moreover
    { fix m assume A3: "m\<in>\<int>\<^sub>+"
      with A1 have "f\<inverse>(m) \<in> \<int>"
	using Int_ZF_2_4_L2 PositiveSet_def by simp 
      with II have "f`(f\<inverse>(m)) \<lsq> f`(f\<inverse>(m)\<rs>\<one>) \<ra> M"
	by simp
      moreover from A1 A2 I A3 have "f`(f\<inverse>(m)\<rs>\<one>) \<ra> M \<lsq> m\<ra>M"
	using Int_ZF_2_4_L4 int_ord_transl_inv by simp
      ultimately have "f`(f\<inverse>(m)) \<lsq> m\<ra>M"
	by (rule Int_order_transitive)
      moreover from A1 A3 have "m \<lsq> f`(f\<inverse>(m))"
	using Int_ZF_2_4_L2 by simp
      moreover from A1 A2 T A3 have "f`(f\<inverse>(m)) = (f\<circ>?h)`(m)"
	using Int_ZF_2_4_L9 Int_ZF_1_5_L11
	  Int_ZF_2_4_L10 PositiveSet_def Int_ZF_2_1_L10
	by simp
      ultimately have "m \<lsq> (f\<circ>?h)`(m) \<and> (f\<circ>?h)`(m) \<lsq> m\<ra>M"
	by simp }
    ultimately show "f\<circ>?h \<sim> id(\<int>)" using Int_ZF_2_1_L32
      by simp
  qed 
  ultimately show "\<exists>h\<in>\<S>. f\<circ>h \<sim> id(\<int>)"
    by auto
qed

text\<open>\<open>Int_ZF_2_4_L12\<close> is almost what we need, except that it has an assumption
  that the values of the slope that we get the inverse for are not smaller than $2$ on
  positive integers. The Arthan's proof of Theorem 11 has a mistake where he says "note that
  for all but finitely many $m,n\in N$ $p=g(m)$ and $q=g(n)$ are both positive". Of course
  there may be infinitely many pairs $\langle m,n \rangle$ such that $p,q$ are not both 
  positive. This is however easy to workaround: we just modify the slope by adding a 
  constant so that the slope is large enough on positive integers and then look 
  for the inverse.\<close>

theorem (in int1) pos_slope_has_inv: assumes A1: "f \<in> \<S>\<^sub>+"
  shows "\<exists>g\<in>\<S>. f\<sim>g \<and> (\<exists>h\<in>\<S>. g\<circ>h \<sim> id(\<int>))"
proof -
  from A1 have "f: \<int>\<rightarrow>\<int>"  "\<one>\<in>\<int>"  "\<two> \<in> \<int>"
    using AlmostHoms_def int_zero_one_are_int int_two_three_are_int
    by auto
  moreover from A1 have
     "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)"
    using Int_ZF_2_3_L5 by simp
  ultimately have 
    "\<exists>c\<in>\<int>. \<two> \<lsq> Minimum(IntegerOrder,{n\<in>\<int>\<^sub>+. \<one> \<lsq> f`(n)\<ra>c})"
    by (rule Int_ZF_1_6_L7)
  then obtain c where I: "c\<in>\<int>" and
    II: "\<two> \<lsq> Minimum(IntegerOrder,{n\<in>\<int>\<^sub>+. \<one> \<lsq> f`(n)\<ra>c})"
    by auto
  let ?g = "{\<langle>m,f`(m)\<ra>c\<rangle>. m\<in>\<int>}"
  from A1 I have III: "?g\<in>\<S>" and IV: "f\<sim>?g" using Int_ZF_2_1_L33 
    by auto
  from IV have "\<langle>f,?g\<rangle> \<in> AlEqRel" by simp
  with A1 have T: "?g \<in> \<S>\<^sub>+" by (rule Int_ZF_2_3_L9)
  moreover have "\<forall>m\<in>\<int>\<^sub>+. ?g\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
  proof
    fix m assume A2: "m\<in>\<int>\<^sub>+"
    from A1 I II have V: "\<two> \<lsq> ?g\<inverse>(\<one>)"
      using Int_ZF_2_1_L33 PositiveSet_def by simp
    moreover from A2 T have "?g\<inverse>(\<one>) \<lsq> ?g\<inverse>(m)"
      using Int_ZF_1_5_L3 int_one_two_are_pos Int_ZF_2_4_L5
      by simp
    ultimately have "\<two> \<lsq> ?g\<inverse>(m)"
      by (rule Int_order_transitive)
    then have "\<two>\<rs>\<one> \<lsq> ?g\<inverse>(m)\<rs>\<one>"
      using int_zero_one_are_int Int_ZF_1_1_L4 int_ord_transl_inv
      by simp
    then show  "?g\<inverse>(m)\<rs>\<one> \<in> \<int>\<^sub>+"
      using int_zero_one_are_int Int_ZF_1_2_L3 Int_ZF_1_5_L3
      by simp
  qed
  ultimately have "\<exists>h\<in>\<S>. ?g\<circ>h \<sim> id(\<int>)"
    by (rule Int_ZF_2_4_L12)
  with III IV show ?thesis by auto
qed

subsection\<open>Completeness\<close>

text\<open>In this section we consider properties of slopes that are
  needed for the proof of completeness of real numbers constructred
  in \<open>Real_ZF_1.thy\<close>. In particular we consider properties
  of embedding of integers into the set of slopes by the mapping
  $m \mapsto m^S$ , where $m^S$ is defined by $m^S(n) = m\cdot n$.\<close>

text\<open>If m is an integer, then $m^S$ is a slope whose value
  is $m\cdot n$ for every integer.\<close>

lemma (in int1) Int_ZF_2_5_L1: assumes A1: "m \<in> \<int>"
  shows 
  "\<forall>n \<in> \<int>. (m\<^sup>S)`(n) = m\<cdot>n"
  "m\<^sup>S \<in> \<S>"
proof -
  from A1 have I: "m\<^sup>S:\<int>\<rightarrow>\<int>"
    using Int_ZF_1_1_L5 ZF_fun_from_total by simp
  then show II: "\<forall>n \<in> \<int>. (m\<^sup>S)`(n) = m\<cdot>n" using ZF_fun_from_tot_val
    by simp
  { fix n k
    assume A2: "n\<in>\<int>"  "k\<in>\<int>"
    with A1 have T: "m\<cdot>n \<in> \<int>"  "m\<cdot>k \<in> \<int>"
      using Int_ZF_1_1_L5 by auto
    from A1 A2 II T  have "\<delta>(m\<^sup>S,n,k) = m\<cdot>k \<rs> m\<cdot>k"
      using Int_ZF_1_1_L5 Int_ZF_1_1_L1 Int_ZF_1_2_L3
      by simp
    also from T have "\<dots> = \<zero>" using Int_ZF_1_1_L4
      by simp
    finally have "\<delta>(m\<^sup>S,n,k) = \<zero>" by simp
    then have "abs(\<delta>(m\<^sup>S,n,k)) \<lsq> \<zero>"
      using Int_ZF_2_L18 int_zero_one_are_int int_ord_is_refl refl_def
      by simp
  } then have "\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. abs(\<delta>(m\<^sup>S,n,k)) \<lsq> \<zero>"
    by simp
  with I show  "m\<^sup>S \<in> \<S>" by (rule Int_ZF_2_1_L5)
qed

text\<open>For any slope $f$ there is an integer $m$ such that there is some slope $g$ 
  that is almost equal to $m^S$ and dominates $f$ in the sense that $f\leq g$ 
  on positive integers (which implies that either $g$ is almost equal to $f$ or
  $g-f$ is a positive slope. This will be used in \<open>Real_ZF_1.thy\<close> to show
  that for any real number there is an integer that (whose real embedding) 
  is greater or equal.\<close>

lemma (in int1) Int_ZF_2_5_L2: assumes A1: "f \<in> \<S>"
  shows "\<exists>m\<in>\<int>. \<exists>g\<in>\<S>. (m\<^sup>S\<sim>g \<and> (f\<sim>g \<or> g\<fp>(\<fm>f) \<in> \<S>\<^sub>+))"
proof -
  from A1 have 
    "\<exists>m k. m\<in>\<int> \<and> k\<in>\<int> \<and> (\<forall>p\<in>\<int>. abs(f`(p)) \<lsq> m\<cdot>abs(p)\<ra>k)"
    using Arthan_Lem_8 by simp
  then obtain m k where I: "m\<in>\<int>" and II: "k\<in>\<int>" and 
    III: "\<forall>p\<in>\<int>. abs(f`(p)) \<lsq> m\<cdot>abs(p)\<ra>k"
    by auto
  let ?g = "{\<langle>n,m\<^sup>S`(n) \<ra>k\<rangle>. n\<in>\<int>}"
  from I have IV: "m\<^sup>S \<in> \<S>" using Int_ZF_2_5_L1 by simp
  with II have V: "?g\<in>\<S>" and VI: "m\<^sup>S\<sim>?g" using Int_ZF_2_1_L33 
    by auto
  { fix n assume A2: "n\<in>\<int>\<^sub>+"
    with A1 have "f`(n) \<in> \<int>"
      using Int_ZF_2_1_L2B PositiveSet_def by simp
    then have "f`(n) \<lsq> abs(f`(n))" using Int_ZF_2_L19C 
      by simp
    moreover  
    from III A2 have "abs(f`(n)) \<lsq> m\<cdot>abs(n) \<ra> k"
      using PositiveSet_def by simp
    with A2 have "abs(f`(n)) \<lsq> m\<cdot>n\<ra>k"
      using Int_ZF_1_5_L4A by simp
    ultimately have "f`(n) \<lsq> m\<cdot>n\<ra>k"
      by (rule Int_order_transitive)
    moreover
    from II IV A2 have "?g`(n) = (m\<^sup>S)`(n)\<ra>k"
      using Int_ZF_2_1_L33 PositiveSet_def by simp
    with I A2 have "?g`(n) = m\<cdot>n\<ra>k"
      using Int_ZF_2_5_L1 PositiveSet_def by simp
    ultimately have "f`(n) \<lsq> ?g`(n)"
      by simp
  } then have "\<forall>n\<in>\<int>\<^sub>+. f`(n) \<lsq> ?g`(n)"
    by simp
  with A1 V have "f\<sim>?g \<or> ?g \<fp> (\<fm>f) \<in> \<S>\<^sub>+"
    using Int_ZF_2_3_L4C by simp
  with I V VI show ?thesis by auto
qed

text\<open>The negative of an integer embeds in slopes as a negative of the 
  orgiginal embedding.\<close>

lemma (in int1) Int_ZF_2_5_L3: assumes A1:  "m \<in> \<int>"
  shows "(\<rm>m)\<^sup>S = \<fm>(m\<^sup>S)"
proof -
  from A1 have "(\<rm>m)\<^sup>S: \<int>\<rightarrow>\<int>" and "(\<fm>(m\<^sup>S)): \<int>\<rightarrow>\<int>"
    using Int_ZF_1_1_L4 Int_ZF_2_5_L1 AlmostHoms_def Int_ZF_2_1_L12
    by auto
  moreover have "\<forall>n\<in>\<int>. ((\<rm>m)\<^sup>S)`(n) = (\<fm>(m\<^sup>S))`(n)"
  proof
    fix n assume A2: "n\<in>\<int>"
    with A1 have 
      "((\<rm>m)\<^sup>S)`(n) = (\<rm>m)\<cdot>n"
      "(\<fm>(m\<^sup>S))`(n) = \<rm>(m\<cdot>n)"
      using Int_ZF_1_1_L4 Int_ZF_2_5_L1 Int_ZF_2_1_L12A
      by auto
    with A1 A2 show "((\<rm>m)\<^sup>S)`(n) = (\<fm>(m\<^sup>S))`(n)"
      using Int_ZF_1_1_L5 by simp
  qed
  ultimately show "(\<rm>m)\<^sup>S = \<fm>(m\<^sup>S)" using fun_extension_iff
    by simp
qed


text\<open>The sum of embeddings is the embeding of the sum.\<close>

lemma (in int1) Int_ZF_2_5_L3A: assumes A1: "m\<in>\<int>"  "k\<in>\<int>"
  shows "(m\<^sup>S) \<fp> (k\<^sup>S) = ((m\<ra>k)\<^sup>S)"
proof -
  from A1 have T1: "m\<ra>k \<in> \<int>" using Int_ZF_1_1_L5 
    by simp
  with A1 have T2:
    "(m\<^sup>S) \<in> \<S>"  "(k\<^sup>S) \<in> \<S>"
    "(m\<ra>k)\<^sup>S  \<in> \<S>"
    "(m\<^sup>S) \<fp> (k\<^sup>S) \<in> \<S>"
    using Int_ZF_2_5_L1 Int_ZF_2_1_L12C by auto
  then have 
    "(m\<^sup>S) \<fp> (k\<^sup>S) : \<int>\<rightarrow>\<int>"
    "(m\<ra>k)\<^sup>S : \<int>\<rightarrow>\<int>" 
    using AlmostHoms_def by auto
  moreover have "\<forall>n\<in>\<int>. ((m\<^sup>S) \<fp> (k\<^sup>S))`(n) = ((m\<ra>k)\<^sup>S)`(n)"
  proof
    fix n assume A2: "n\<in>\<int>"
    with A1 T1 T2 have  "((m\<^sup>S) \<fp> (k\<^sup>S))`(n) = (m\<ra>k)\<cdot>n"
      using Int_ZF_2_1_L12B Int_ZF_2_5_L1 Int_ZF_1_1_L1
      by simp
    also from T1 A2 have "\<dots> = ((m\<ra>k)\<^sup>S)`(n)"
      using Int_ZF_2_5_L1 by simp
    finally show "((m\<^sup>S) \<fp> (k\<^sup>S))`(n) = ((m\<ra>k)\<^sup>S)`(n)"
      by simp
  qed
  ultimately show "(m\<^sup>S) \<fp> (k\<^sup>S) = ((m\<ra>k)\<^sup>S)"
    using fun_extension_iff by simp
qed

text\<open>The composition of embeddings is the embeding of the product.\<close>

lemma (in int1) Int_ZF_2_5_L3B: assumes A1: "m\<in>\<int>"  "k\<in>\<int>"
  shows "(m\<^sup>S) \<circ> (k\<^sup>S) = ((m\<cdot>k)\<^sup>S)"
proof -
  from A1 have T1: "m\<cdot>k \<in> \<int>" using Int_ZF_1_1_L5 
    by simp
  with A1 have T2:
    "(m\<^sup>S) \<in> \<S>"  "(k\<^sup>S) \<in> \<S>"
    "(m\<cdot>k)\<^sup>S  \<in> \<S>"
    "(m\<^sup>S) \<circ> (k\<^sup>S) \<in> \<S>"
    using Int_ZF_2_5_L1 Int_ZF_2_1_L11 by auto
  then have 
    "(m\<^sup>S) \<circ> (k\<^sup>S) : \<int>\<rightarrow>\<int>"
    "(m\<cdot>k)\<^sup>S : \<int>\<rightarrow>\<int>" 
    using AlmostHoms_def by auto
  moreover have "\<forall>n\<in>\<int>. ((m\<^sup>S) \<circ> (k\<^sup>S))`(n) = ((m\<cdot>k)\<^sup>S)`(n)"
  proof
    fix n assume A2: "n\<in>\<int>"
    with A1 T2 have
      "((m\<^sup>S) \<circ> (k\<^sup>S))`(n) = (m\<^sup>S)`(k\<cdot>n)"
       using Int_ZF_2_1_L10 Int_ZF_2_5_L1 by simp
    moreover
    from A1 A2 have "k\<cdot>n \<in> \<int>" using Int_ZF_1_1_L5 
      by simp
    with A1 A2 have "(m\<^sup>S)`(k\<cdot>n) = m\<cdot>k\<cdot>n"
      using Int_ZF_2_5_L1 Int_ZF_1_1_L7 by simp
    ultimately have "((m\<^sup>S) \<circ> (k\<^sup>S))`(n) = m\<cdot>k\<cdot>n"
      by simp
    also from T1 A2 have "m\<cdot>k\<cdot>n = ((m\<cdot>k)\<^sup>S)`(n)"
      using Int_ZF_2_5_L1 by simp
    finally show "((m\<^sup>S) \<circ> (k\<^sup>S))`(n) = ((m\<cdot>k)\<^sup>S)`(n)"
      by simp
  qed
  ultimately show "(m\<^sup>S) \<circ> (k\<^sup>S) = ((m\<cdot>k)\<^sup>S)"
    using fun_extension_iff by simp
qed
  

text\<open>Embedding integers in slopes preserves order.\<close>

lemma (in int1) Int_ZF_2_5_L4: assumes A1:  "m\<lsq>n"
  shows "(m\<^sup>S) \<sim> (n\<^sup>S) \<or> (n\<^sup>S)\<fp>(\<fm>(m\<^sup>S)) \<in> \<S>\<^sub>+"
proof -
  from A1 have "m\<^sup>S \<in> \<S>" and "n\<^sup>S \<in> \<S>"
    using Int_ZF_2_L1A Int_ZF_2_5_L1 by auto
  moreover from A1 have "\<forall>k\<in>\<int>\<^sub>+. (m\<^sup>S)`(k) \<lsq> (n\<^sup>S)`(k)"
    using Int_ZF_1_3_L13B Int_ZF_2_L1A PositiveSet_def Int_ZF_2_5_L1
    by simp
  ultimately show ?thesis using Int_ZF_2_3_L4C
    by simp
qed

text\<open>We aim at showing that $m\mapsto m^S$ is an injection modulo
  the relation of almost equality. To do that we first show that if
  $m^S$ has finite range, then $m=0$.\<close>

lemma (in int1) Int_ZF_2_5_L5: 
  assumes "m\<in>\<int>" and "m\<^sup>S \<in> FinRangeFunctions(\<int>,\<int>)"
  shows "m=\<zero>"
  using assms FinRangeFunctions_def Int_ZF_2_5_L1 AlmostHoms_def 
    func_imagedef Int_ZF_1_6_L8 by simp

text\<open>Embeddings of two integers are almost equal only if 
  the integers are equal.\<close>

lemma (in int1) Int_ZF_2_5_L6: 
  assumes A1: "m\<in>\<int>"  "k\<in>\<int>" and A2: "(m\<^sup>S) \<sim> (k\<^sup>S)"
  shows "m=k"
proof -
  from A1 have T: "m\<rs>k \<in> \<int>" using Int_ZF_1_1_L5 by simp
  from A1 have "(\<fm>(k\<^sup>S)) =  ((\<rm>k)\<^sup>S)"
    using Int_ZF_2_5_L3 by simp
  then have "m\<^sup>S \<fp> (\<fm>(k\<^sup>S)) = (m\<^sup>S) \<fp> ((\<rm>k)\<^sup>S)"
    by simp
  with A1 have "m\<^sup>S \<fp> (\<fm>(k\<^sup>S)) = ((m\<rs>k)\<^sup>S)"
    using Int_ZF_1_1_L4 Int_ZF_2_5_L3A by simp
  moreover from A1 A2 have "m\<^sup>S \<fp> (\<fm>(k\<^sup>S)) \<in> FinRangeFunctions(\<int>,\<int>)"
    using Int_ZF_2_5_L1 Int_ZF_2_1_L9D by simp
  ultimately have "(m\<rs>k)\<^sup>S \<in> FinRangeFunctions(\<int>,\<int>)"
    by simp
  with T have "m\<rs>k = \<zero>" using Int_ZF_2_5_L5
    by simp
  with A1 show "m=k" by (rule Int_ZF_1_L15)
qed

text\<open>Embedding of $1$ is the identity slope and embedding of zero is a 
  finite range function.\<close>

lemma (in int1) Int_ZF_2_5_L7: shows 
  "\<one>\<^sup>S = id(\<int>)"
  "\<zero>\<^sup>S \<in> FinRangeFunctions(\<int>,\<int>)"
proof -
  have "id(\<int>) = {\<langle>x,x\<rangle>. x\<in>\<int>}"
    using id_def by blast
  then show "\<one>\<^sup>S = id(\<int>)" using Int_ZF_1_1_L4 by simp
  have "{\<zero>\<^sup>S`(n). n\<in>\<int>} = {\<zero>\<cdot>n. n\<in>\<int>}"
    using int_zero_one_are_int Int_ZF_2_5_L1 by simp
  also have "\<dots> = {\<zero>}" using Int_ZF_1_1_L4 int_not_empty
    by simp
  finally have "{\<zero>\<^sup>S`(n). n\<in>\<int>} = {\<zero>}" by simp
  then have "{\<zero>\<^sup>S`(n). n\<in>\<int>} \<in> Fin(\<int>)"
    using int_zero_one_are_int Finite1_L16 by simp
  moreover have "\<zero>\<^sup>S: \<int>\<rightarrow>\<int>" 
    using int_zero_one_are_int Int_ZF_2_5_L1 AlmostHoms_def 
    by simp
  ultimately show "\<zero>\<^sup>S \<in> FinRangeFunctions(\<int>,\<int>)"
    using Finite1_L19 by simp  
qed

text\<open>A somewhat technical condition for a embedding of an integer 
  to be "less  or equal" (in the sense apriopriate for slopes) than 
  the composition of a slope and another integer (embedding).\<close>

lemma (in int1) Int_ZF_2_5_L8: 
  assumes A1: "f \<in> \<S>" and A2: "N \<in> \<int>"  "M \<in> \<int>" and
  A3: "\<forall>n\<in>\<int>\<^sub>+. M\<cdot>n \<lsq> f`(N\<cdot>n)"
  shows "M\<^sup>S \<sim> f\<circ>(N\<^sup>S) \<or>  (f\<circ>(N\<^sup>S)) \<fp> (\<fm>(M\<^sup>S)) \<in> \<S>\<^sub>+"
proof -
  from A1 A2 have "M\<^sup>S \<in> \<S>"  "f\<circ>(N\<^sup>S) \<in> \<S>"
    using Int_ZF_2_5_L1 Int_ZF_2_1_L11 by auto
  moreover from A1 A2 A3 have "\<forall>n\<in>\<int>\<^sub>+. (M\<^sup>S)`(n) \<lsq> (f\<circ>(N\<^sup>S))`(n)"
    using Int_ZF_2_5_L1 PositiveSet_def Int_ZF_2_1_L10
    by simp
  ultimately show ?thesis using Int_ZF_2_3_L4C
    by simp
qed

text\<open>Another technical condition for the composition of a slope and 
  an integer (embedding) to be "less  or equal" (in the sense apriopriate 
  for slopes) than embedding of another integer.\<close>

lemma (in int1) Int_ZF_2_5_L9: 
  assumes A1: "f \<in> \<S>" and A2: "N \<in> \<int>"  "M \<in> \<int>" and
  A3: "\<forall>n\<in>\<int>\<^sub>+.  f`(N\<cdot>n) \<lsq> M\<cdot>n "
  shows "f\<circ>(N\<^sup>S) \<sim> (M\<^sup>S) \<or> (M\<^sup>S) \<fp> (\<fm>(f\<circ>(N\<^sup>S))) \<in> \<S>\<^sub>+"
proof -
  from A1 A2 have "f\<circ>(N\<^sup>S) \<in> \<S>"  "M\<^sup>S \<in> \<S>"  
    using Int_ZF_2_5_L1 Int_ZF_2_1_L11 by auto
  moreover from A1 A2 A3 have "\<forall>n\<in>\<int>\<^sub>+. (f\<circ>(N\<^sup>S))`(n) \<lsq> (M\<^sup>S)`(n) "
    using Int_ZF_2_5_L1 PositiveSet_def Int_ZF_2_1_L10
    by simp
  ultimately show ?thesis using Int_ZF_2_3_L4C
    by simp
qed

end