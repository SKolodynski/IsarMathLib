(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024 Daniel de la Concepcion

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Ultraproduct construction\<close>

theory UltraConstruction_ZF imports Ultrafilter_ZF EquivClass1
begin

text\<open>This theory deals with the ultra product construction, internal entities
and some basic properties of them.\<close>

locale ultra = 
  fixes \<FF> and I and X
  assumes ultraFilter:"\<FF>{is an ultrafilter on}I" and nonEmpty:"\<forall>i\<in>I. X(i)\<noteq>0"

begin

text\<open>We define an equivalence relation\<close>

definition hyper_rel where
"hyper_rel \<equiv> {\<langle>f,g\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. f`n = g`n}\<in>\<FF>}"

text\<open>The relation is reflexive\<close>

lemma hyper_refl:
  shows "refl(Pi(I,X),hyper_rel)" unfolding refl_def
proof-
  {
    fix x assume x:"x:Pi(I,X)"
    have "{n\<in>I. x`n = x`n} = I" by auto moreover
    have "I\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
    ultimately have "{n\<in>I. x`n = x`n}\<in>\<FF>" by auto
    with x have "\<langle>x,x\<rangle>\<in>hyper_rel" unfolding hyper_rel_def by auto
  }
  then show "\<forall>x\<in>Pi(I, X). \<langle>x, x\<rangle> \<in> hyper_rel" by auto
qed

text\<open>The relation is symmetric\<close>

lemma hyper_sym:
  shows "sym(hyper_rel)" unfolding sym_def
proof(safe)
  fix x y assume "\<langle>x, y\<rangle> \<in> hyper_rel"
  then have as:"x:Pi(I,X)" "y:Pi(I,X)" "{n\<in>I. x`n = y`n}\<in>\<FF>" unfolding hyper_rel_def by auto
  {
    fix n assume "n\<in>{n\<in>I. x`n = y`n}"
    then have "n\<in>I" "x`n=y`n" by auto
    then have "n\<in>{n\<in>I. y`n = x`n}" by auto
  } moreover
  {
    fix n assume "n\<in>{n\<in>I. y`n = x`n}"
    then have "n\<in>I" "y`n=x`n" by auto
    then have "n\<in>{n\<in>I. x`n = y`n}" by auto
  } ultimately
  have "{n\<in>I. y`n = x`n} = {n\<in>I. x`n = y`n}" by blast
  with as(3) have "{n\<in>I. y`n = x`n} :\<FF>" by auto
  with as(1,2) show "\<langle>y,x\<rangle>\<in>hyper_rel" unfolding hyper_rel_def by auto
qed

text\<open>The relation is transitive\<close>

lemma hyper_trans:
  shows "trans(hyper_rel)" unfolding trans_def
proof(safe)
  fix x y z assume as:"\<langle>x, y\<rangle> \<in> hyper_rel" "\<langle>y, z\<rangle> \<in> hyper_rel"
  then have A:"x:Pi(I,X)" "z:Pi(I,X)" unfolding hyper_rel_def by auto
  {
    fix n assume "n\<in>{n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n}"
    then have "n\<in>{n\<in>I. x`n = z`n}" by auto
  }
  then have sub:"{n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n} \<subseteq> {n\<in>I. x`n = z`n}" by auto
  from as(1,2) have "{n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n}:\<FF>" using ultraFilter
    unfolding hyper_rel_def IsUltrafilter_def IsFilter_def by auto
  then have "\<forall>A\<in>Pow(I). {n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n} \<subseteq> A \<longrightarrow> A\<in>\<FF>"
    using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  moreover have "{n\<in>I. x`n = z`n}\<in>Pow(I)" by auto
  ultimately have "({n\<in>I. x`n = y`n}\<inter>{n\<in>I. y`n = z`n} \<subseteq> {n\<in>I. x`n = z`n}) \<longrightarrow> {n\<in>I. x`n = z`n}\<in>\<FF>"
    by auto
  with sub have "{n\<in>I. x`n = z`n}\<in>\<FF>" by auto
  with A show "\<langle>x, z\<rangle> \<in> hyper_rel" unfolding hyper_rel_def by auto
qed

text\<open>The relation is an equivalence\<close>

lemma hyper_equiv:
  shows "equiv(Pi(I,X), hyper_rel)" unfolding equiv_def
  using hyper_refl hyper_sym hyper_trans apply auto
  unfolding hyper_rel_def by auto

definition hyper_set where
"hyper_set \<equiv> Pi(I,X)// hyper_rel"

lemma incl_inj:
  fixes Y
  assumes "\<forall>i\<in>I. X(i) = Y"
  defines "incl \<equiv> {\<langle>x,hyper_rel``{ConstantFunction(I,x)}\<rangle>. x\<in>Y}"
  shows "incl\<in>inj(Y,hyper_set)" unfolding inj_def
proof(safe)
  {
    fix x assume x:"x:Y"
    then have "ConstantFunction(I,x):I\<rightarrow>Y" using func1_3_L1 by auto
    then have "ConstantFunction(I,x)\<in>Pi(I,X)" unfolding Pi_def Sigma_def using assms(1) by auto
    then have "hyper_rel``{ConstantFunction(I,x)}\<in>hyper_set" unfolding hyper_set_def
      quotient_def by auto
  }
  then have "\<forall>x\<in>Y. hyper_rel``{ConstantFunction(I,x)}\<in>hyper_set" by auto
  then show f:"incl:Y\<rightarrow>hyper_set" using ZF_fun_from_total unfolding incl_def by auto
  {
    fix w x assume as:"w:Y" "x:Y" "incl ` w = incl ` x"
    then have e:"hyper_rel``{ConstantFunction(I,w)} = hyper_rel``{ConstantFunction(I,x)}"
      using apply_equality[OF _ f] unfolding incl_def by auto
    from as(1,2) have c:"ConstantFunction(I,w):I\<rightarrow>Y" "ConstantFunction(I,x):I\<rightarrow>Y"
      using func1_3_L1 by auto
    then have cc:"ConstantFunction(I,w)\<in>Pi(I,X)" "ConstantFunction(I,x):Pi(I,X)" unfolding Pi_def Sigma_def using assms(1) by auto
    with e have "\<langle>ConstantFunction(I,w),ConstantFunction(I,x)\<rangle>\<in>hyper_rel" using same_image_equiv[of "Pi(I,X)" "hyper_rel"]
      hyper_equiv by auto
    then have "{n\<in>I. ConstantFunction(I,w)`n = ConstantFunction(I,x)`n}:\<FF>"
      unfolding hyper_rel_def by auto
    then have "{n\<in>I. w = x}:\<FF>" using func1_3_L2 by auto
    then show "w=x" using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  }
qed

lemma hyper_set_structure:
  assumes "\<forall>i\<in>I. P(i):X(i)\<times>X(i)\<rightarrow>X(i)"
  defines "Q \<equiv> {\<langle>\<langle>q1,q2\<rangle>,{\<langle>i,P(i)`\<langle>q1`i,q2`i\<rangle>\<rangle>. i\<in>I}\<rangle>. \<langle>q1,q2\<rangle>\<in>Pi(I,X)\<times>Pi(I,X)}"
  shows "Congruent2(hyper_rel, Q)" "Q:Pi(I,X)\<times>Pi(I,X) \<rightarrow> Pi(I,X)"
    "\<forall>i\<in>I. \<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle>`i = P(i)`\<langle>x`i,y`i\<rangle>"
  unfolding Congruent2_def hyper_rel_def apply safe apply auto
proof-
  {
    fix x y assume xy:"x\<in>Pi(I,X)" "y\<in>Pi(I,X)"
    {
      fix i assume i:"i:I"
      with xy have "x`i:X(i)" "y`i:X(i)" using apply_type by auto
      with assms(1) have "P(i)`\<langle>x`i,y`i\<rangle>\<in>X(i)" using apply_type i by auto
    }
    then have "{\<langle>i,P(i)`\<langle>x`i,y`i\<rangle>\<rangle>. i\<in>I}:Pi(I,X)"
      unfolding Pi_def function_def by auto
  }
  then have "\<forall>x\<in>Pi(I, X) \<times> Pi(I, X).
       (\<lambda>\<langle>q1,q2\<rangle>. {\<langle>i, P(i) ` \<langle>q1 ` i, q2 ` i\<rangle>\<rangle> . i \<in> I})(x) \<in> Pi(I, X)" by auto moreover
  have "Q={\<langle>x, (\<lambda>\<langle>q1,q2\<rangle>. {\<langle>i, P(i) ` \<langle>q1 ` i, q2 ` i\<rangle>\<rangle> . i \<in> I})(x)\<rangle> . x \<in> Pi(I, X) \<times> Pi(I, X)}"
    unfolding Q_def by force
  ultimately show qF:"Q:Pi(I,X)\<times>Pi(I,X)\<rightarrow>Pi(I,X)" unfolding Q_def 
    using ZF_fun_from_total[of "Pi(I,X)\<times>Pi(I,X)" "\<lambda>\<langle>q1,q2\<rangle>. {\<langle>i,P(i)`\<langle>q1`i,q2`i\<rangle>\<rangle>. i\<in>I}" "Pi(I,X)"]
    by auto
  then have "\<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle> = {\<langle>i,P(i)`\<langle>x`i,y`i\<rangle>\<rangle>. i\<in>I}"
    using apply_equality unfolding Q_def by auto moreover
  from qF have "\<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle>\<in>Pi(I,X)"
    using apply_type by auto ultimately
  have R:"\<forall>i\<in>I. \<forall>x\<in>Pi(I,X). \<forall>y\<in>Pi(I,X). Q`\<langle>x,y\<rangle>`i = P(i)`\<langle>x`i,y`i\<rangle>"
    using apply_equality[where A=I and B=X] by auto
  then show "\<And>i x y. i \<in> I \<Longrightarrow> x \<in> Pi(I, X) \<Longrightarrow> y \<in> Pi(I, X) \<Longrightarrow> Q ` \<langle>x, y\<rangle> ` i = P(i) ` \<langle>x ` i, y ` i\<rangle>" by auto
  fix x y z t
  assume as:"{n \<in> I . x ` n = y ` n} \<in> \<FF>"
       "x \<in> Pi(I,X)" "y \<in> Pi(I,X)" "{n \<in> I . z ` n = t ` n} \<in> \<FF>"
       "z \<in> Pi(I,X)" "t \<in> Pi(I,X)"
  from qF as(2,5) show "Q`\<langle>x,z\<rangle>:Pi(I,X)" using apply_type by auto
  from qF as(3,6) show "Q`\<langle>y,t\<rangle>:Pi(I,X)" using apply_type by auto
  {
    fix n assume "n\<in>{n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n}"
    then have "n\<in>I" "x ` n = y ` n" "z ` n = t ` n" by auto
    then have "P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>" by auto
    with `n\<in>I` have "n\<in>{n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}" by auto
  }
  then have "{n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}"
    by blast
  moreover from as(1,4) have "{n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n}:\<FF>"
    using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  then have "\<forall>A\<in>Pow(I). {n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> A \<longrightarrow> A:\<FF>"
    using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
  then have "{n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}\<in>Pow(I) \<longrightarrow> (({n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}) \<longrightarrow> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}:\<FF>)"
    by auto
  then have "({n \<in> I . x ` n = y ` n}\<inter>{n \<in> I . z ` n = t ` n} \<subseteq> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}) \<longrightarrow> {n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}:\<FF>" by auto
  ultimately have "{n \<in> I . P(n)`\<langle>x`n,z`n\<rangle> = P(n)`\<langle>y`n,t`n\<rangle>}:\<FF>" by auto
  then show "{n \<in> I . Q`\<langle>x,z\<rangle>`n = Q`\<langle>y,t\<rangle>`n}:\<FF>"
    using R as(2,3,5,6) by auto
qed

subsection\<open>Internal sets\<close>

definition internal_set where
"S:Pi(I,\<lambda>i. Pow(X(i))) \<Longrightarrow> internal_set(S) \<equiv> {hyper_rel``{x}. x\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>S`n}\<in>\<FF>}}"

lemma internal_subset:
  assumes "S:Pi(I,\<lambda>i. Pow(X(i)))"
  shows "internal_set(S) \<subseteq> hyper_set"
proof-
  {
    fix t assume "t\<in>internal_set(S)"
    then have "t\<in>{hyper_rel``{x}. x\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>S`n}\<in>\<FF>}}"
      unfolding internal_set_def[OF assms].
    then obtain q where q:"t=hyper_rel``{q}" "q:Pi(I,X)" "{n\<in>I. q`n\<in>S`n}\<in>\<FF>"
      by auto
    from q(1,2) have "t\<in>hyper_set" unfolding hyper_set_def quotient_def by auto
  }
  then show "internal_set(S) \<subseteq> hyper_set" by auto
qed

lemma internal_sub:
  assumes "S1:Pi(I,\<lambda>i. Pow(X(i)))"  "S2:Pi(I,\<lambda>i. Pow(X(i)))" "{n\<in>I. S1`n \<subseteq> S2`n}\<in>\<FF>"
  shows "internal_set(S1) \<subseteq> internal_set(S2)"
proof
  fix x assume "x\<in>internal_set(S1)"
  then obtain xx where x:"xx\<in>Pi(I,X)" "x=hyper_rel``{xx}" "{n\<in>I. xx`n\<in>S1`n}\<in>\<FF>"
    unfolding internal_set_def[OF assms(1)] by auto
  from x(3) assms(3) have "{n\<in>I. S1`n \<subseteq> S2`n}\<inter>{n\<in>I. xx`n\<in>S1`n}\<in>\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  moreover have "{n\<in>I. xx`n\<in>S2`n}\<in>Pow(I)" by auto
  moreover have "{n\<in>I. S1`n \<subseteq> S2`n}\<inter>{n\<in>I. xx`n\<in>S1`n} \<subseteq> {n\<in>I. xx`n\<in>S2`n}" by auto
  ultimately have "{n\<in>I. xx`n\<in>S2`n}\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  with x(1,2) show "x\<in>internal_set(S2)" unfolding internal_set_def[OF assms(2)] by auto
qed

lemma internal_sub_rev:
  assumes "S1:Pi(I,\<lambda>i. Pow(X(i)))"  "S2:Pi(I,\<lambda>i. Pow(X(i)))" 
  and "internal_set(S1) \<subseteq> internal_set(S2)"
  and "Pi({i\<in>I. \<not>(S1`i\<subseteq>S2`i)},\<lambda>j. S1`j-S2`j) \<noteq> 0" (* We can choose elements in the difference*)
  and "Pi(I,X)\<noteq>0"
  shows "{n\<in>I. S1`n \<subseteq> S2`n}\<in>\<FF>"
proof-
  from assms(5) obtain y where y:"y\<in>Pi(I,X)" by auto
  from assms(4) obtain x where x:"x\<in>Pi({i\<in>I. \<not>(S1`i\<subseteq>S2`i)},\<lambda>j. S1`j-S2`j)" by auto
  let ?u="{\<langle>i,if S1`i\<subseteq>S2`i then y`i else x`i\<rangle>. i\<in>I}"
  {
    fix n assume "n\<in>I"
    {
      assume "S1`n \<subseteq> S2`n"
      then have "(if S1`n\<subseteq>S2`n then y`n else x`n) = y`n" by auto
      then have "(if S1`n\<subseteq>S2`n then y`n else x`n)\<in>X(n)" using apply_type `n\<in>I` y by auto
    } moreover
    {
      assume as:"\<not>(S1`n \<subseteq> S2`n)"
      then have "(if S1`n\<subseteq>S2`n then y`n else x`n) = x`n" by auto
      moreover have "n\<in>{i\<in>I. \<not>(S1`i\<subseteq>S2`i)}" using `n\<in>I` as by auto
      then have "x`n\<in>S1`n - S2`n" using apply_type[OF x, of n] by auto
      ultimately have "(if S1`n\<subseteq>S2`n then y`n else x`n)\<in>S1`n-S2`n" using apply_type x `n\<in>I` x as by auto
      then have "(if S1`n\<subseteq>S2`n then y`n else x`n)\<in>S1`n" by auto
      then have "(if S1`n\<subseteq>S2`n then y`n else x`n)\<in>X(n)" using apply_type[OF assms(1) `n\<in>I`] by blast 
    }
    ultimately have "(if S1`n\<subseteq>S2`n then y`n else x`n)\<in>X(n)" by auto
  }
  then have u:"?u\<in>Pi(I,X)" unfolding Pi_def function_def by auto
  then have R:"\<And>n. n\<in>I \<Longrightarrow> \<not>(S1`n \<subseteq> S2`n) \<Longrightarrow> ?u`n=x`n" using apply_equality by auto
  {
    assume as:"{n\<in>I. S1`n \<subseteq> S2`n}\<notin>\<FF>"
    with as have "I-{n\<in>I. S1`n \<subseteq> S2`n}\<in>\<FF>" using ultraFilter set_ultrafilter[of _ I \<FF>] by auto
    moreover have "{n\<in>I. \<not>(S1`n \<subseteq> S2`n)} = I-{n\<in>I. S1`n \<subseteq> S2`n}" by auto
    ultimately have F1:"{n\<in>I. \<not>(S1`n \<subseteq> S2`n)}\<in>\<FF>" by auto
    {
      fix j assume "j\<in>{n\<in>I. \<not>(S1`n \<subseteq> S2`n)}"
      then have j:"j\<in>I" "\<not>(S1`j \<subseteq> S2`j)" by auto
      with x have "x`j \<in> S1`j - S2`j" using apply_type[OF x] by auto
      then have "x`j\<in>S1`j" "x`j\<notin>S2`j" by auto
      with R j have "?u`j\<in>S1`j" "?u`j\<notin>S2`j" by auto
    }
    then have F2:"{n\<in>I. \<not>(S1`n \<subseteq> S2`n)} \<subseteq> {n\<in>I. ?u`n\<in>S1`n}" "{n\<in>I. \<not>(S1`n \<subseteq> S2`n)} \<subseteq> {n\<in>I. ?u`n\<notin>S2`n}" by auto
    from ultraFilter have "\<And>C. C\<subseteq>I \<Longrightarrow> {n\<in>I. \<not>(S1`n \<subseteq> S2`n)} \<subseteq> C \<Longrightarrow> C\<in>\<FF>"
      using F1 unfolding IsUltrafilter_def IsFilter_def by auto
    then have "{n\<in>I. ?u`n\<in>S1`n}\<subseteq>I \<Longrightarrow> {n\<in>I. \<not>(S1`n \<subseteq> S2`n)} \<subseteq> {n\<in>I. ?u`n\<in>S1`n} \<Longrightarrow> {n\<in>I. ?u`n\<in>S1`n}\<in>\<FF>"
     "{n\<in>I. ?u`n\<notin>S2`n}\<subseteq>I \<Longrightarrow> {n\<in>I. \<not>(S1`n \<subseteq> S2`n)} \<subseteq> {n\<in>I. ?u`n\<notin>S2`n} \<Longrightarrow> {n\<in>I. ?u`n\<notin>S2`n}\<in>\<FF>" by auto
    with F2 have U:"{n\<in>I. ?u`n\<in>S1`n}\<in>\<FF>" "{n\<in>I. ?u`n\<notin>S2`n}\<in>\<FF>" by auto
    from U(1) u have u1:"hyper_rel``{?u}\<in>internal_set(S1)" unfolding internal_set_def[OF assms(1)]
      by auto
    have "I-{n\<in>I. ?u`n\<in>S2`n} = {n\<in>I. ?u`n\<notin>S2`n}" by auto
    with U(2) have "I-{n\<in>I. ?u`n\<in>S2`n}\<in>\<FF>" by auto
    then have "I-(I-{n\<in>I. ?u`n\<in>S2`n})\<notin>\<FF>" using ultraFilter only_set_or_opposite[of "I-{n\<in>I. ?u`n\<in>S2`n}" I]
      unfolding IsUltrafilter_def by auto
    moreover have "I-(I-{n\<in>I. ?u`n\<in>S2`n}) = {n\<in>I. ?u`n\<in>S2`n}" by auto
    ultimately have M:"{n\<in>I. ?u`n\<in>S2`n}\<notin>\<FF>" by auto
    {
      fix q assume "q\<in>Pi(I,X)" "hyper_rel``{q} = hyper_rel``{?u}"
      then have "\<langle>q,?u\<rangle>\<in>hyper_rel" using same_image_equiv[OF hyper_equiv] u by auto
      then have A:"{n\<in>I. q`n = ?u`n}\<in>\<FF>" unfolding hyper_rel_def by auto
      {
        assume "{n\<in>I. q`n\<in>S2`n}\<in>\<FF>"
        with A have AA:"{n\<in>I. q`n = ?u`n}\<inter>{n\<in>I. q`n\<in>S2`n}\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def
          using is_filter_def_split(4) by auto
        moreover have B:"{n\<in>I. q`n = ?u`n}\<inter>{n\<in>I. q`n\<in>S2`n} \<subseteq> {n\<in>I. ?u`n\<in>S2`n}" by auto
        from AA ultraFilter have "\<And>C. C\<subseteq> I \<Longrightarrow> {n\<in>I. q`n = ?u`n}\<inter>{n\<in>I. q`n\<in>S2`n} \<subseteq> C \<Longrightarrow> C\<in>\<FF>"
          unfolding IsUltrafilter_def using is_filter_def_split(5) by auto
        then have "{n\<in>I. ?u`n\<in>S2`n}\<subseteq>I \<Longrightarrow>{n\<in>I. q`n = ?u`n}\<inter>{n\<in>I. q`n\<in>S2`n} \<subseteq> {n\<in>I. ?u`n\<in>S2`n} \<Longrightarrow> {n\<in>I. ?u`n\<in>S2`n}\<in>\<FF>" 
          by auto
        then have "{n\<in>I. q`n = ?u`n}\<inter>{n\<in>I. q`n\<in>S2`n} \<subseteq> {n\<in>I. ?u`n\<in>S2`n} \<Longrightarrow> {n\<in>I. ?u`n\<in>S2`n}\<in>\<FF>" by auto
        with B have "{n\<in>I. ?u`n\<in>S2`n}\<in>\<FF>" by auto
        with M have False by auto
      }
      then have "{n\<in>I. q`n\<in>S2`n}\<notin>\<FF>" by auto
    }
    then have "hyper_rel``{?u}\<notin>internal_set(S2)" unfolding internal_set_def[OF assms(2)] by auto
    with u1 assms(3) have False by auto
  }
  then show ?thesis by auto
qed

corollary internal_eq:
  assumes "S1:Pi(I,\<lambda>i. Pow(X(i)))"  "S2:Pi(I,\<lambda>i. Pow(X(i)))" "{n\<in>I. S1`n = S2`n}\<in>\<FF>"
  shows "internal_set(S1) = internal_set(S2)"
proof
  have "{n\<in>I. S1`n = S2`n} \<subseteq> {n\<in>I. S1`n \<subseteq> S2`n}" "{n\<in>I. S1`n = S2`n} \<subseteq> {n\<in>I. S2`n \<subseteq> S1`n}" by auto
  moreover have "{n\<in>I. S1`n \<subseteq> S2`n}:Pow(I)" "{n\<in>I. S2`n \<subseteq> S1`n}:Pow(I)" by auto
  moreover note assms(3) ultimately have A:"{n\<in>I. S1`n \<subseteq> S2`n}:\<FF>" "{n\<in>I. S2`n \<subseteq> S1`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  from A(1) show "internal_set(S1) \<subseteq> internal_set(S2)" using internal_sub[OF assms(1,2)] by auto
  from A(2) show "internal_set(S2) \<subseteq> internal_set(S1)" using internal_sub[OF assms(2,1)] by auto
qed

lemma internal_total_set:
  shows "internal_set({\<langle>i,X(i)\<rangle>. i\<in>I}) = hyper_set"
proof
  have f:"{\<langle>i,X(i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume "t\<in>internal_set({\<langle>i,X(i)\<rangle>. i\<in>I})"
    then have "t\<in>{hyper_rel``{x}. x\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}}"
      unfolding internal_set_def[OF f].
    then obtain q where q:"t=hyper_rel``{q}" "q:Pi(I,X)" "{n\<in>I. q`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>"
      by auto
    from q(1,2) have "t\<in>hyper_set" unfolding hyper_set_def quotient_def by auto
  }
  then show "internal_set({\<langle>i,X(i)\<rangle>. i\<in>I}) \<subseteq> hyper_set" by auto
  {
    fix t assume "t\<in>hyper_set"
    then obtain q where q:"t=hyper_rel``{q}" "q:Pi(I,X)" unfolding hyper_set_def
        quotient_def by auto
    from f have R:"\<forall>n\<in>I. {\<langle>i,X(i)\<rangle>. i\<in>I}`n = X(n)" using apply_equality by auto
    from q(2) have "\<forall>n\<in>I. q`n\<in>X(n)" using apply_type by auto
    then have "{n\<in>I. q`n\<in>X(n)} = I" by auto
    then have "{n\<in>I. q`n\<in>X(n)}\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def IsFilter_def
      by auto
    with R have "{n\<in>I. q`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>" by auto
    with q(2) have "q\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}" by auto
    with q(1) have "t\<in>{hyper_rel``{x}. x\<in>{x\<in>Pi(I,X). {n\<in>I. x`n\<in>{\<langle>i,X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}}" by auto
    then have "t:internal_set({\<langle>i,X(i)\<rangle>. i\<in>I})" unfolding internal_set_def[OF f].
  }
  then show "hyper_set \<subseteq> internal_set({\<langle>i,X(i)\<rangle>. i\<in>I})" by auto
qed

definition isInternal where
"isInternal(Y) \<equiv> \<exists>S\<in>Pi(I,\<lambda>i. Pow(X(i))). Y=internal_set(S)" 

corollary total_inter:
  shows "isInternal(hyper_set)"
proof-
  have "{\<langle>i,X(i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  then show ?thesis unfolding isInternal_def using internal_total_set[THEN sym] by auto
qed

lemma internal_inter:
  assumes "isInternal(A)" "isInternal(B)"
  shows "isInternal(A\<inter>B)"
proof-
  from assms obtain SA SB where s:"SA:Pi(I,\<lambda>i. Pow(X(i)))" "SB:Pi(I,\<lambda>i. Pow(X(i)))" 
    "A=internal_set(SA)" "B=internal_set(SB)"
    unfolding isInternal_def by auto
  let ?S="{\<langle>n,(SA`n)\<inter>(SB`n)\<rangle>. n\<in>I}"
  from s(1,2) have "\<forall>n\<in>I. (SA`n)\<in>Pow(X(n))" "\<forall>n\<in>I. (SB`n)\<in>Pow(X(n))" using apply_type[of _ I "\<lambda>i. Pow(X(i))"]
    by auto
  then have "\<forall>n\<in>I. (SA`n)\<inter>(SB`n)\<in>Pow(X(n))" by auto
  then have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?S)"
    then obtain x where x:"t=hyper_rel``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>"
      unfolding internal_set_def[OF f] by auto
    from x(3) have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)}\<in>\<FF>"
      using apply_equality[OF _ f] by auto
    then have R:"\<forall>A\<in>Pow(I). {n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> A \<longrightarrow> A\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    moreover have "{n\<in>I. x`n\<in>SA`n}\<in>Pow(I)" by auto
    ultimately have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SA`n} \<longrightarrow> {n\<in>I. x`n\<in>SA`n}\<in>\<FF>" by auto
    moreover have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SA`n}" by auto
    ultimately have "{n\<in>I. x`n\<in>SA`n}\<in>\<FF>" by auto
    with x(1,2) have A:"t\<in>internal_set(SA)" unfolding internal_set_def[OF s(1)] by auto
    have "{n\<in>I. x`n\<in>SB`n}\<in>Pow(I)" by auto
    with R have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SB`n} \<longrightarrow> {n\<in>I. x`n\<in>SB`n}\<in>\<FF>" by auto
    moreover have "{n\<in>I. x`n\<in>(SA`n)\<inter>(SB`n)} \<subseteq> {n\<in>I. x`n\<in>SB`n}" by auto
    ultimately have "{n\<in>I. x`n\<in>SB`n}\<in>\<FF>" by auto
    with x(1,2) have "t\<in>internal_set(SB)" unfolding internal_set_def[OF s(2)] by auto
    with A have "t\<in>A\<inter>B" using s(3,4) by auto
  }
  then have "internal_set(?S) \<subseteq> A\<inter>B" by auto moreover
  {
    fix t assume t:"t\<in>A\<inter>B"
    with s(3,4) obtain ta tb where t:"t=hyper_rel``{ta}" "ta\<in>Pi(I,X)" "{n\<in>I. ta`n\<in>SA`n}\<in>\<FF>"
      "t=hyper_rel``{tb}" "tb\<in>Pi(I,X)" "{n\<in>I. tb`n\<in>SB`n}\<in>\<FF>" unfolding internal_set_def[OF s(1)]
      internal_set_def[OF s(2)] by blast
    from t(1,4) have "hyper_rel``{ta}=hyper_rel``{tb}" by auto
    then have "\<langle>ta,tb\<rangle>\<in>hyper_rel" using same_image_equiv[OF hyper_equiv] t(5) by auto
    then have "{n\<in>I. ta`n=tb`n}:\<FF>" unfolding hyper_rel_def by auto
    with t(3) have "{n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    with t(6) have "{n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}\<inter>{n\<in>I. tb`n\<in>SB`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<forall>A\<in>Pow(I). {n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}\<inter>{n\<in>I. tb`n\<in>SB`n}\<subseteq>A \<longrightarrow> A:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    moreover have "{n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n} :Pow(I)" by auto
    ultimately have "{n\<in>I. ta`n=tb`n}\<inter>{n\<in>I. ta`n\<in>SA`n}\<inter>{n\<in>I. tb`n\<in>SB`n}\<subseteq>{n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n} \<longrightarrow> {n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n}:\<FF>"
      by auto
    then have "{n\<in>I. ta`n\<in>(SA`n)\<inter>SB`n}:\<FF>" by auto
    then have "{n\<in>I. ta`n\<in>{\<langle>n, SA ` n \<inter> SB ` n\<rangle> . n \<in> I}`n}:\<FF>"
      using apply_equality[OF _ f] by auto
    with t(1,2) have "t\<in>internal_set(?S)" unfolding internal_set_def[OF f] by auto
  }
  then have "A\<inter>B \<subseteq> internal_set(?S)" by auto
  ultimately have "A\<inter>B = internal_set(?S)" by auto
  then show ?thesis unfolding isInternal_def using f by auto
qed

text\<open>The complement of an internal set is internal\<close>

lemma complement_internal:
  assumes "isInternal(A)"
  shows "isInternal(hyper_set-A)"
proof-
  from assms obtain SA where s:"SA:Pi(I,\<lambda>i. Pow(X(i)))"
    "A=internal_set(SA)" unfolding isInternal_def by auto
  let ?S="{\<langle>n,X(n)-(SA`n)\<rangle>. n\<in>I}"
  have "\<forall>n\<in>I. X(n)-(SA`n)\<in>Pow(X(n))" by auto
  then have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?S)"
    then obtain x where x:"t=hyper_rel``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>"
      unfolding internal_set_def[OF f] by auto
    {
      assume "t\<in>internal_set(SA)"
      then obtain y where y:"t=hyper_rel``{y}" "y\<in>Pi(I,X)" "{n\<in>I. y`n\<in>SA`n}\<in>\<FF>"
        unfolding internal_set_def[OF s(1)] by auto
      from x(1) y(1) have "\<langle>x,y\<rangle>\<in>hyper_rel" using y(2) same_image_equiv
          hyper_equiv by auto
      then have "{n\<in>I. x`n = y`n}\<in>\<FF>" unfolding hyper_rel_def by auto
      with y(3) have "{n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n}\<in>\<FF>"
        using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      then have "\<And>A. A\<in>Pow(I) \<Longrightarrow> {n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n} \<subseteq> A \<Longrightarrow> A:\<FF>"
        using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      then have "{n\<in>I. x`n\<in>SA`n}\<in>Pow(I) \<Longrightarrow> {n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n} \<subseteq> {n\<in>I. x`n\<in>SA`n} \<Longrightarrow> {n\<in>I. x`n\<in>SA`n}:\<FF>" by auto
      moreover have "{n\<in>I. y`n\<in>SA`n}\<inter>{n\<in>I. x`n = y`n} \<subseteq> {n\<in>I. x`n\<in>SA`n}" by auto
      ultimately have "{n\<in>I. x`n\<in>SA`n}: \<FF>" by auto
      with x(3) have "{n\<in>I. x`n\<in>SA`n}\<inter>{n\<in>I. x`n\<in>X(n)-(SA`n)}\<in>\<FF>" using ultraFilter
        apply_equality[OF _ f]
        unfolding IsUltrafilter_def IsFilter_def by auto moreover
      {
        fix n assume n:"n\<in>{n\<in>I. x`n\<in>SA`n}\<inter>{n\<in>I. x`n\<in>X(n)-(SA`n)}"
        then have False by auto
      }
      then have "{n\<in>I. x`n\<in>SA`n}\<inter>{n\<in>I. x`n\<in>X(n)-(SA`n)} = 0" by auto
      ultimately have "0\<in>\<FF>" by auto
      then have False using ultraFilter
        unfolding IsUltrafilter_def IsFilter_def by auto
    }
    then have "t\<notin>internal_set(SA)" by auto moreover
    have "t\<in>hyper_set" using internal_subset[OF f] t by auto
    ultimately have "t\<in>hyper_set-A" using s(2) by auto
  }
  then have "internal_set(?S) \<subseteq> hyper_set-A" by auto moreover
  {
    fix t assume "t\<in>hyper_set-A"
    then have t:"t\<in>hyper_set" "t\<notin>A" by auto
    from t(1) obtain x where x:"t=hyper_rel``{x}" "x:Pi(I,X)" unfolding hyper_set_def
      quotient_def by auto
    with t(2) s(2) have "{n\<in>I. x`n\<in>SA`n}\<notin>\<FF>" unfolding internal_set_def[OF s(1)] by auto
    then have "I-{n\<in>I. x`n\<in>SA`n}\<in>\<FF>" using set_ultrafilter[OF _ ultraFilter]
      by auto
    then have "{n\<in>I. x`n\<in>X(n)-SA`n}\<in>Pow(I) \<Longrightarrow> I-{n\<in>I. x`n\<in>SA`n} \<subseteq> {n\<in>I. x`n\<in>X(n)-SA`n} \<longrightarrow> {n\<in>I. x`n\<in>X(n)-SA`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix q assume "q\<in>I-{n\<in>I. x`n\<in>SA`n}"
      then have "q: I" "x`q\<notin>SA`q" by auto
      with x(2) have "q\<in>I" "x`q:X(q)" "x`q\<notin>SA`q" using apply_type by auto
      then have "q\<in>{n\<in>I. x`n\<in>X(n)-SA`n}" by auto
    }
    then have "I-{n\<in>I. x`n\<in>SA`n} \<subseteq> {n\<in>I. x`n\<in>X(n)-SA`n}" by auto ultimately
    have "{n\<in>I. x`n\<in>X(n)-SA`n}\<in>\<FF>" by auto
    then have "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>" using apply_equality[OF _ f] by auto
    with x(1,2) have "t\<in>internal_set(?S)" unfolding internal_set_def[OF f] by auto
  }
  ultimately have "hyper_set-A = internal_set(?S)" by auto
  then show ?thesis unfolding isInternal_def using f by auto
qed

lemma finite_internal:
  assumes "A\<in>FinPow(hyper_set)"
  shows "isInternal(A)" unfolding isInternal_def
proof(rule FinPow_induct[OF _ _ assms])
  let ?S0="I\<times>{0}"
  have s:"?S0:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume "t\<in>internal_set(?S0)"
    then obtain x where x:"t=hyper_rel``{x}" "x:Pi(I,X)" "{n\<in>I. x`n\<in>?S0`n}\<in>\<FF>"
      unfolding internal_set_def[OF s] by auto
    from x(3) have "{n\<in>I. x`n\<in>0}\<in>\<FF>" using apply_equality[OF _ s] by auto
    then have "0\<in>\<FF>" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then have "0 = internal_set(?S0)" by auto
  with s show "\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). 0 = internal_set(S)" by auto
  {
    fix B assume b:"B\<in>FinPow(hyper_set)" "\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). B = internal_set(S)"
    from b(2) obtain S where S:"S:(\<Prod>i\<in>I. Pow(X(i)))" "B=internal_set(S)" by auto

    {
      fix t assume "t\<in>hyper_set"
      then obtain x where x:"t=hyper_rel``{x}" "x:Pi(I,X)" unfolding hyper_set_def
        quotient_def by auto
      let ?S="{\<langle>i,S`i\<union>{x`i}\<rangle>. i\<in>I}"
      have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def apply auto
        using apply_type[OF x(2)] apply_type[OF S(1)] by auto
      {
        fix q assume q:"q\<in>B\<union>{t}"
        {
          assume "q\<in>B"
          with S(2) obtain y where y:"q=hyper_rel``{y}" "y:Pi(I,X)" "{n\<in>I. y`n\<in>S`n}:\<FF>"
            unfolding internal_set_def[OF S(1)] by auto
          have "{n\<in>I. y`n\<in>S`n} \<subseteq> {n\<in>I. y`n\<in>S`n\<union>{x`n}}" by auto
          moreover from y(3) have "\<And>Q. Q \<subseteq> I \<Longrightarrow> {n\<in>I. y`n\<in>S`n} \<subseteq> Q \<Longrightarrow> Q:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          from this[of "{n\<in>I. y`n\<in>S`n\<union>{x`n}}"] 
          have "{n\<in>I. y`n\<in>S`n} \<subseteq> {n\<in>I. y`n\<in>S`n\<union>{x`n}} \<Longrightarrow> {n\<in>I. y`n\<in>S`n\<union>{x`n}}:\<FF>" by auto
          ultimately have "{n\<in>I. y`n\<in>S`n\<union>{x`n}}:\<FF>" by auto
          then have "{n\<in>I. y`n\<in>?S`n}:\<FF>" using apply_equality[OF _ f] by auto
          with y(1,2) have "q\<in>internal_set(?S)" unfolding internal_set_def[OF f] by auto
        } moreover
        {
          assume "q\<notin>B"
          with q have "q=t" by auto
          with x have xx:"q=hyper_rel``{x}" "x:Pi(I,X)" by auto
          have "{n\<in>I. x`n\<in>{x`n}} = I" by auto
          then have "{n\<in>I. x`n\<in>{x`n}}\<in>\<FF>" using ultraFilter unfolding IsFilter_def
            IsUltrafilter_def by auto
          then have "\<And>Q. Q \<subseteq> I \<Longrightarrow> {n\<in>I. x`n\<in>{x`n}} \<subseteq> Q \<Longrightarrow> Q:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          from this[of "{n:I. x`n:?S`n}"] have 
            "{n\<in>I. x`n\<in>{x`n}} \<subseteq> {n:I. x`n:?S`n} \<Longrightarrow> {n:I. x`n:?S`n}:\<FF>" by auto
          moreover
          have "{n\<in>I. x`n\<in>{x`n}} \<subseteq> {n:I. x`n:?S`n}" using apply_equality[OF _ f] by auto
          ultimately have " {n:I. x`n:?S`n}:\<FF>" by auto
          with xx have "q\<in>internal_set(?S)" unfolding internal_set_def[OF f] by auto
        } ultimately
        have "q:internal_set(?S)" by auto
      }
      then have "B\<union>{t} \<subseteq> internal_set(?S)" by auto moreover
      {
        fix q assume q:"q\<in>internal_set(?S)" "q\<noteq>t"
        then obtain y where y:"q=hyper_rel``{y}" "y:Pi(I,X)" "{n:I. y`n:?S`n}:\<FF>"
          unfolding internal_set_def[OF f] by auto
        {
          assume "{n\<in>I. y`n\<in>S`n}\<notin>\<FF>"
          then have "I-{n\<in>I. y`n\<in>S`n}\<in>\<FF>" using ultraFilter
            set_ultrafilter[of _ I, OF _ ultraFilter] by auto
          with y(3) have "(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n}:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          then have "\<And>B. B:Pow(I) \<Longrightarrow> (I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n} \<subseteq> B \<Longrightarrow> B:\<FF>"
            using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
          from this[of "{n:I. y`n=x`n}"] have "(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n} \<subseteq> {n:I. y`n=x`n} \<Longrightarrow> {n:I. y`n=x`n}:\<FF>"
            by auto moreover
          {
            fix h assume "h:(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n}"
            then have "h\<in>I" "y`h\<notin>S`h" "y`h\<in>?S`h" by auto
            then have "h\<in>I" "y`h = x`h" using apply_equality[OF _ f] by auto
            then have "h:{n:I. y`n=x`n}" by auto
          }
          then have "(I-{n\<in>I. y`n\<in>S`n})\<inter>{n:I. y`n:?S`n} \<subseteq> {n:I. y`n=x`n}" by auto
          ultimately have "{n:I. y`n=x`n}:\<FF>" by auto
          with x(2) y(2) have "\<langle>y,x\<rangle>:hyper_rel" unfolding hyper_rel_def by auto
          then have "q=t" using x(1) y(1) equiv_class_eq[OF hyper_equiv] by auto
          with q(2) have False by auto
        }
        then have "{n\<in>I. y`n\<in>S`n}\<in>\<FF>" by auto
        with y(1,2) have "q\<in>B" using S(2) unfolding internal_set_def[OF S(1)] by auto
      }
      then have "internal_set(?S) \<subseteq> B\<union>{t}" by auto
      ultimately have "B\<union>{t} = internal_set(?S)" by auto
      with f have "\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). B \<union> {t} = internal_set(S)" by auto
    }
    then have "\<forall>t\<in>hyper_set. \<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). B \<union> {t} = internal_set(S)" by auto
  }
  then show "\<forall>A\<in>FinPow(hyper_set).
       (\<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). A = internal_set(S)) \<longrightarrow>
       (\<forall>t\<in>hyper_set. \<exists>S\<in>\<Prod>i\<in>I. Pow(X(i)). A \<union> {t} = internal_set(S))" by auto
qed

lemma internal_union:
  assumes "isInternal(A)" "isInternal(B)"
  shows "isInternal(A\<union>B)"
proof-
  from assms obtain SA SB where s:"SA:Pi(I,\<lambda>i. Pow(X(i)))" "SB:Pi(I,\<lambda>i. Pow(X(i)))" 
    "A=internal_set(SA)" "B=internal_set(SB)"
    unfolding isInternal_def by auto
  let ?S="{\<langle>n,(SA`n)\<union>(SB`n)\<rangle>. n\<in>I}"
  from s(1,2) have "\<forall>n\<in>I. (SA`n)\<in>Pow(X(n))" "\<forall>n\<in>I. (SB`n)\<in>Pow(X(n))" using apply_type[of _ I "\<lambda>i. Pow(X(i))"]
    by auto
  then have "\<forall>n\<in>I. (SA`n)\<union>(SB`n)\<in>Pow(X(n))" by auto
  then have f:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?S)"
    then obtain x where x:"t=hyper_rel``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>?S`n}\<in>\<FF>"
      unfolding internal_set_def[OF f] by auto
    from x(3) have U:"{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<in>\<FF>"
      using apply_equality[OF _ f] by auto
    {
      assume "t\<notin>A"
      with x(1,2) s(3) have "{n\<in>I. x`n\<in>(SA`n)}\<notin>\<FF>" unfolding internal_set_def[OF s(1)]
        by auto
      then have "I-{n\<in>I. x`n\<in>(SA`n)}\<in>\<FF>" using ultraFilter
        set_ultrafilter[of "{n\<in>I. x`n\<in>(SA`n)}"] by auto moreover
      have "{n\<in>I. x`n\<notin>(SA`n)}\<in>Pow(I)" by auto moreover
      {
        fix n assume "n\<in>I-{n\<in>I. x`n\<in>(SA`n)}"
        then have "n\<in>{n\<in>I. x`n\<notin>(SA`n)}" by auto
      }
      then have "I-{n\<in>I. x`n\<in>(SA`n)} \<subseteq> {n\<in>I. x`n\<notin>(SA`n)}" by auto
      ultimately have "{n\<in>I. x`n\<notin>(SA`n)}:\<FF>" using ultraFilter unfolding IsFilter_def
        IsUltrafilter_def by auto
      with U have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<inter>{n\<in>I. x`n\<notin>(SA`n)}:\<FF>"
        using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
      have "{n:I. x`n\<in>SB`n}\<in>Pow(I)" by auto moreover
      {
        fix n assume "n\<in>{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<inter>{n\<in>I. x`n\<notin>(SA`n)}"
        then have "n\<in>I" "x`n\<in>SB`n" by auto
        then have "n:{n:I. x`n\<in>SB`n}" by auto
      }
      then have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<inter>{n\<in>I. x`n\<notin>(SA`n)} \<subseteq> {n:I. x`n\<in>SB`n}" by auto
      ultimately have "{n:I. x`n\<in>SB`n}\<in>\<FF>" using ultraFilter unfolding IsFilter_def
        IsUltrafilter_def by auto
      with x(1,2) have "t\<in>B" using s(4) unfolding internal_set_def[OF s(2)] by auto
    }
    then have "t\<in>A\<union>B" by auto
  }
  then have "internal_set(?S) \<subseteq> A\<union>B" by auto moreover
  {
    fix t assume "t\<in>A"
    then obtain x where x:"t=hyper_rel``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>SA`n}\<in>\<FF>"
      using s(3) unfolding internal_set_def[OF s(1)] by auto
    have "{n\<in>I. x`n\<in>SA`n} \<subseteq> {n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}" by auto moreover
    have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<in>Pow(I)" by auto moreover note x(3)
    ultimately have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>I. x`n\<in>?S`n}:\<FF>" using apply_equality[OF _ f] by auto
    with x(1,2) have "t\<in>internal_set(?S)" unfolding internal_set_def[OF f] by auto
  }
  then have "A \<subseteq> internal_set(?S)" by auto moreover
  {
    fix t assume "t\<in>B"
    then obtain x where x:"t=hyper_rel``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>SB`n}\<in>\<FF>"
      using s(4) unfolding internal_set_def[OF s(2)] by auto
    have "{n\<in>I. x`n\<in>SB`n} \<subseteq> {n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}" by auto moreover
    have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}\<in>Pow(I)" by auto moreover note x(3)
    ultimately have "{n\<in>I. x`n\<in>(SA`n)\<union>(SB`n)}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>I. x`n\<in>?S`n}:\<FF>" using apply_equality[OF _ f] by auto
    with x(1,2) have "t\<in>internal_set(?S)" unfolding internal_set_def[OF f] by auto
  }
  then have "B \<subseteq> internal_set(?S)" by auto ultimately
  have "A \<union> B = internal_set(?S)" by auto
  then show ?thesis unfolding isInternal_def using f by auto
qed

definition elevatedProp ("^_^" 90) where
"^P^ \<equiv> \<lambda>t. \<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y}=t"

lemma internal_subset_internal:
  assumes "isInternal(A)"
  shows "isInternal({x\<in>A. (^P^)(x)})"
proof-
  from assms obtain S where s:"S:Pi(I,\<lambda>i. Pow(X(i)))"
    "A=internal_set(S)" unfolding isInternal_def by auto
  let ?S="{\<langle>i,{x\<in>S`i. P(x)}\<rangle>. i\<in>I}"
  {
    fix i assume i:"i\<in>I"
    then have "{x\<in>S`i. P(x)} \<subseteq> S`i" by auto
    with s(1) have "{x\<in>S`i. P(x)} \<subseteq> X(i)" using apply_type[OF _ i, of S "\<lambda>i. Pow(X(i))"] by auto  
  }
  then have ss:"?S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def function_def by auto
  {
    fix t assume "t\<in>{x\<in>A. \<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y} = x}"
    then obtain y where t:"t\<in>A" "y\<in>Pi(I,X)" "{i\<in>I. P(y`i)}\<in>\<FF>" "hyper_rel``{y} = t" by auto
    from t(1,4) have "hyper_rel``{y}\<in>internal_set(S)" using s(2) by auto
    then obtain z where z:"hyper_rel``{y} = hyper_rel``{z}" "z\<in>Pi(I,X)" "{i\<in>I. z`i\<in>S`i}\<in>\<FF>"
      unfolding internal_set_def[OF s(1)] by auto
    from z(1) have "\<langle>y,z\<rangle>\<in>hyper_rel" using same_image_equiv[OF hyper_equiv] z(2) by auto
    then have "{i\<in>I. y`i = z`i}\<in>\<FF>" unfolding hyper_rel_def by auto
    with z(3) have "{i\<in>I. y`i = z`i}\<inter>{i\<in>I. z`i\<in>S`i}\<in>\<FF>" using ultraFilter
      unfolding IsUltrafilter_def IsFilter_def by auto
    moreover have "{i\<in>I. y`i = z`i}\<inter>{i\<in>I. z`i\<in>S`i} = {i\<in>I. y`i = z`i \<and> y`i\<in>S`i}" by auto
    ultimately have "{i\<in>I. y`i = z`i \<and> y`i\<in>S`i}\<in>\<FF>" by auto moreover
    have "{i\<in>I. y`i = z`i \<and> y`i\<in>S`i} \<subseteq> {i\<in>I. y`i\<in>S`i}" by auto moreover
    have "\<And>C. C\<subseteq>I \<Longrightarrow> {i\<in>I. y`i = z`i \<and> y`i\<in>S`i} \<subseteq> C \<Longrightarrow> {i\<in>I. y`i = z`i \<and> y`i\<in>S`i}\<in>\<FF> \<Longrightarrow> C\<in>\<FF>" 
      using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
    then have "{i\<in>I. y`i\<in>S`i} \<subseteq> I \<Longrightarrow> {i\<in>I. y`i = z`i \<and> y`i\<in>S`i} \<subseteq> {i\<in>I. y`i\<in>S`i} \<Longrightarrow> {i\<in>I. y`i = z`i \<and> y`i\<in>S`i}\<in>\<FF> \<Longrightarrow> {i\<in>I. y`i\<in>S`i}\<in>\<FF>" by auto
    ultimately have "{i\<in>I. y`i\<in>S`i}\<in>\<FF>" by auto
    with t(3) have "{i\<in>I. y`i\<in>S`i}\<inter>{i\<in>I. P(y`i)}\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def 
      IsFilter_def by auto moreover
    have "{i\<in>I. y`i\<in>S`i}\<inter>{i\<in>I. P(y`i)} = {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}}" by auto
    ultimately have "{i\<in>I. y`i\<in>{x\<in>S`i. P(x)}}\<in>\<FF>" by auto
    then have "{i\<in>I. y`i\<in>?S`i}\<in>\<FF>" using apply_equality[OF _ ss] by auto
    with t(2,4) have "t\<in>internal_set(?S)" unfolding internal_set_def[OF ss] by auto
  }
  then have "{x\<in>A. \<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y} = x} \<subseteq> internal_set(?S)" by auto moreover
  {
    fix t assume "t\<in>internal_set(?S)"
    then obtain y where t:"t=hyper_rel``{y}" "y\<in>Pi(I,X)" "{i\<in>I. y`i\<in>?S`i}\<in>\<FF>"
      unfolding internal_set_def[OF ss] by auto
    from t(3) have "{i\<in>I. y`i\<in>{x\<in>S`i. P(x)}}\<in>\<FF>" using apply_equality ss by auto
    moreover have "{i\<in>I. y`i\<in>{x\<in>S`i. P(x)}} \<subseteq> {i\<in>I. y`i\<in>S`i}" "{i\<in>I. y`i\<in>{x\<in>S`i. P(x)}} \<subseteq> {i\<in>I. P(y`i)}" by auto
    moreover have "\<And>C. C\<subseteq>I \<Longrightarrow> {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}} \<subseteq> C \<Longrightarrow> {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}}\<in>\<FF> \<Longrightarrow> C\<in>\<FF>" 
      using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
    then have "{i\<in>I. y`i\<in>S`i}\<subseteq>I \<Longrightarrow> {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}} \<subseteq> {i\<in>I. y`i\<in>S`i} \<Longrightarrow> {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}}\<in>\<FF> \<Longrightarrow> {i\<in>I. y`i\<in>S`i}\<in>\<FF>" 
      "{i\<in>I. P(y`i)}\<subseteq>I \<Longrightarrow> {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}} \<subseteq> {i\<in>I. P(y`i)} \<Longrightarrow> {i\<in>I. y`i\<in>{x\<in>S`i. P(x)}}\<in>\<FF> \<Longrightarrow> {i\<in>I. P(y`i)}\<in>\<FF>" by auto
    ultimately have "{i\<in>I. y`i\<in>S`i}\<in>\<FF>" "{i\<in>I. P(y`i)}\<in>\<FF>" by auto
    with t(1,2) have "t\<in>internal_set(S)" "\<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y} = t"
      unfolding internal_set_def[OF s(1)] by auto
    with s(2) have "t\<in>{x\<in>A. \<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y} = x}" by auto
  }
  then have "internal_set(?S) \<subseteq> {x\<in>A. \<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y} = x}" by auto
  ultimately have "{x\<in>A. \<exists>y\<in>Pi(I,X). {i\<in>I. P(y`i)}\<in>\<FF> \<and> hyper_rel``{y} = x} = internal_set(?S)" by auto
  then show ?thesis unfolding isInternal_def using ss unfolding elevatedProp_def by auto
qed

          
definition internal_rel where
"S:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i))) \<Longrightarrow> internal_rel(S) \<equiv> {\<langle>hyper_rel``{x},hyper_rel``{y}\<rangle>. \<langle>x,y\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>S`n}\<in>\<FF>}}"

lemma internal_rel_subset:
  assumes "S:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))"
  shows "internal_rel(S) \<subseteq> hyper_set\<times>hyper_set"
proof-
  {
    fix t assume "t\<in>internal_rel(S)"
    then have "t\<in>{\<langle>hyper_rel``{x},hyper_rel``{y}\<rangle>. \<langle>x,y\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>S`n}\<in>\<FF>}}"
      unfolding internal_rel_def[OF assms].
    then obtain q p where q:"t=\<langle>hyper_rel``{q},hyper_rel``{p}\<rangle>" "q:Pi(I,X)" "p:Pi(I,X)" "{n\<in>I. \<langle>q`n,p`n\<rangle>\<in>S`n}\<in>\<FF>"
      by auto
    from q(1-3) have "t\<in>hyper_set\<times>hyper_set" unfolding hyper_set_def quotient_def by auto
  }
  then show "internal_rel(S) \<subseteq> hyper_set\<times>hyper_set" by auto
qed

lemma converse_internal:
  assumes "S:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))"
  shows "converse(internal_rel(S)) = internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I})"
proof
  have "\<And>i. i\<in>I \<Longrightarrow> (S`i) \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms] by auto
  then have "\<And>i. i\<in>I \<Longrightarrow> converse(S`i) \<subseteq> X(i)\<times>X(i)" unfolding converse_def by auto
  then have A:"{\<langle>i,converse(S`i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))" unfolding Pi_def function_def by auto
  {
    fix x assume "x\<in>converse(internal_rel(S))"
    then obtain y z where x:"x=\<langle>y,z\<rangle>" "\<langle>z,y\<rangle>\<in>internal_rel(S)" using converse_iff by auto
    from x(2) obtain zz yy where q:"zz:Pi(I,X)" "yy:Pi(I,X)" "z=hyper_rel``{zz}"  "y=hyper_rel``{yy}" 
      "{n \<in> I . \<langle>zz ` n, yy ` n\<rangle> \<in> S ` n} \<in> \<FF>" 
      unfolding internal_rel_def[OF assms] by auto
    from q(5) have "{n \<in> I . \<langle>yy ` n, zz ` n\<rangle> \<in> converse(S ` n)}:\<FF>" using converse_iff by auto
    then have "{n \<in> I . \<langle>yy ` n, zz ` n\<rangle> \<in> {\<langle>i,converse(S`i)\<rangle>. i\<in>I}`n}:\<FF>" using apply_equality[OF _ A] by auto
    with q(1-4) x(1) have "x\<in>internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I})" unfolding internal_rel_def[OF A] by auto
  }
  then show "converse(internal_rel(S)) \<subseteq> internal_rel({\<langle>i, converse(S ` i)\<rangle> . i \<in> I})" by auto
  {
    fix x assume "x\<in>internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I})"
    then obtain zz yy where q:"zz:Pi(I,X)" "yy:Pi(I,X)" "x=\<langle>hyper_rel``{zz},hyper_rel``{yy}\<rangle>" 
      "{n \<in> I . \<langle>zz ` n, yy ` n\<rangle> \<in> {\<langle>i,converse(S`i)\<rangle>. i\<in>I} ` n} \<in> \<FF>" 
      unfolding internal_rel_def[OF A] by auto
    from q(4) have "{n \<in> I . \<langle>zz ` n, yy ` n\<rangle> \<in> converse(S ` n)} \<in> \<FF>"  using apply_equality[OF _ A] by auto
    then have "{n \<in> I . \<langle>yy ` n, zz ` n\<rangle> \<in> (S ` n)} \<in> \<FF>" using converse_iff by auto
    then have "\<langle>hyper_rel``{yy},hyper_rel``{zz}\<rangle>\<in>internal_rel(S)" unfolding internal_rel_def[OF assms]
      using q(1,2) by auto
    then have "x:converse(internal_rel(S))" using q(3) converse_iff by auto
  }
  then show "internal_rel({\<langle>i,converse(S`i)\<rangle>. i\<in>I}) \<subseteq> converse(internal_rel(S))" by auto
qed
    

lemma internal_rel_total:
  shows "internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}) = hyper_set\<times>hyper_set"
proof
  have f:"{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}:Pi(I,\<lambda>i. Pow(X(i)\<times>X(i)))" unfolding Pi_def function_def by auto
  then show "internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}) \<subseteq> hyper_set\<times>hyper_set" using internal_rel_subset by auto
  {
    fix m assume "m\<in>hyper_set\<times>hyper_set"
    then obtain m1 m2 where p:"m1\<in>hyper_set" "m2\<in>hyper_set" "m=\<langle>m1,m2\<rangle>" by auto
    then obtain x1 x2 where m:"m1=hyper_rel``{x1}" "m2=hyper_rel``{x2}" "m=\<langle>m1,m2\<rangle>"
      "x1\<in>Pi(I,X)" "x2\<in>Pi(I,X)" unfolding hyper_set_def quotient_def by auto
    {
      fix n assume n:"n\<in>I"
      with m have "\<langle>x1`n,x2`n\<rangle>\<in>X(n)\<times>X(n)" using apply_type by auto
      then have "\<langle>x1`n,x2`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n" using apply_equality[OF _ f] n by auto
    }
    then have "I={n\<in>I. \<langle>x1`n,x2`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}" by auto
    then have "{n\<in>I. \<langle>x1`n,x2`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}:\<FF>" using
        ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<langle>x1,x2\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}"
      using m(4,5) by auto
    with m(1,2) have "\<langle>m1,m2\<rangle>\<in>{\<langle>hyper_rel``{x1},hyper_rel``{x2}\<rangle>. \<langle>x1,x2\<rangle>\<in>{\<langle>p,q\<rangle>\<in>Pi(I,X)\<times>Pi(I,X). {n\<in>I. \<langle>p`n,q`n\<rangle>\<in>{\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I}`n}\<in>\<FF>}}"
      by auto
    with p(3) have "m\<in>internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I})"
      unfolding internal_rel_def[OF f] by auto
  }
  then show "hyper_set\<times>hyper_set \<subseteq> internal_rel({\<langle>i,X(i)\<times>X(i)\<rangle>. i\<in>I})" by auto
qed

end
end
