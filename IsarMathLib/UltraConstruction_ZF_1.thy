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

section \<open>Internal functions in ultraproduct construction\<close>

theory UltraConstruction_ZF_1 imports UltraConstruction_ZF begin

text\<open>This theory continues \<open>UltraConstruction_ZF\<close> with results about internal functions — functions whose fibres are elements of an internal family.\<close>

context ultra begin

subsection\<open>Internal functions\<close>

definition internal_fun where
"S1:Pi(I,\<lambda>i. Pow(X(i))) \<Longrightarrow> S2:Pi(I,\<lambda>i. Pow(X(i))) \<Longrightarrow> S:Pi(I, \<lambda>i. S1`i \<rightarrow> S2`i) 
  \<Longrightarrow> internal_fun(S) \<equiv> internal_rel(S)"


lemma internal_fun_is_fun:
  assumes "S1:Pi(I,\<lambda>i. Pow(X(i)))" "S2:Pi(I,\<lambda>i. Pow(X(i)))" "S:Pi(I, \<lambda>i. S1`i \<rightarrow> S2`i)"
  shows "internal_fun(S):internal_set(S1)\<rightarrow>internal_set(S2)" "S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))" unfolding Pi_def function_def
proof(safe)
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  from SS show "\<And>x. x \<in> S \<Longrightarrow> x \<in> (\<Sum>i\<in>I. Pow(X(i) \<times> X(i)))" unfolding Pi_def by auto
  from SS show "\<And>x. x \<in> I \<Longrightarrow> x \<in> domain(S)" unfolding Pi_def by auto
  from SS show "\<And>x y y'. \<langle>x, y\<rangle> \<in> S \<Longrightarrow> \<langle>x, y'\<rangle> \<in> S \<Longrightarrow> y = y'" unfolding Pi_def function_def by blast
  fix x assume x:"x\<in>internal_fun(S)"
  then obtain y z where f:"x= \<langle>hyper_rel``{y},hyper_rel``{z}\<rangle>" "y:Pi(I,X)" "z:Pi(I,X)" "{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n}\<in>\<FF>"
    unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] by auto
  {
    fix n assume n:"n:{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n}"
    then have n:"n:I" "\<langle>y`n,z`n\<rangle>:S`n" by auto
    moreover from n(1) have "S`n\<in> S1`n \<rightarrow> S2`n" using apply_type[OF assms(3)] by auto
    with n(2) have "y`n:S1`n" "z`n:S2`n" unfolding Pi_def by auto
    with n(1) have "n\<in>{n:I. y`n:S1`n}" "n\<in>{n:I. z`n:S2`n}" by auto
  }
  then have s:"{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n} \<subseteq> {n:I. y`n:S1`n}" "{n\<in>I. \<langle>y`n, z`n\<rangle>:S`n} \<subseteq> {n:I. z`n:S2`n}" by auto
  from f(4) have R:"\<And>A. A\<in>Pow(I) \<Longrightarrow> {n\<in>I. \<langle>y`n, z`n\<rangle>:S`n} \<subseteq> A \<Longrightarrow> A\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  from R[of "{n:I. y`n:S1`n}"] s(1) have "{n:I. y`n:S1`n}\<in>\<FF>" by auto
  then have "hyper_rel``{y}:internal_set(S1)" unfolding internal_set_def[OF assms(1)]
    using f(2) by auto moreover
  from R[of "{n:I. z`n:S2`n}"] s(2) have "{n:I. z`n:S2`n}\<in>\<FF>" by auto
  then have "hyper_rel``{z}:internal_set(S2)" unfolding internal_set_def[OF assms(2)]
    using f(3) by auto moreover note f(1)
  ultimately show "x\<in>internal_set(S1)\<times>internal_set(S2)" by auto
next
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  fix x assume "x\<in>internal_set(S1)"
  then obtain y where x:"x=hyper_rel``{y}" "y:Pi(I,X)" "{n:I. y`n\<in>S1`n}:\<FF>"
    unfolding internal_set_def[OF assms(1)] by auto
  let ?z="{\<langle>i,if y`i\<in>S1`i then (S`i)`(y`i) else y`i\<rangle>. i\<in>I}"
  have z:"?z\<in>Pi(I,X)" unfolding Pi_def function_def apply auto prefer 2
    using x(2) apply_type apply simp
  proof-
    fix i assume i:"i:I" "y ` i \<in> S1 ` i"
    from i(1) assms(3) have "S`i:S1`i \<rightarrow> S2`i" using apply_type by auto
    with i(2) have "(S`i)`(y`i):S2`i" using apply_type by auto
    with i(1) show "(S`i)`(y`i):X(i)" using apply_type[OF assms(2)] by auto
  qed
  {
    fix n assume "n\<in>{n:I. y`n\<in>S1`n}"
    then have n:"n:I" "y`n:S1`n" by auto
    from assms(3) n(1) have "S`n\<in>S1`n \<rightarrow> S2`n" using apply_type by auto
    with n(2) have "\<langle>y`n,(S`n)`(y`n)\<rangle>\<in>S`n" using apply_Pair by auto
    with n(1) have "n\<in>{n:I.  \<langle>y`n, ?z`n\<rangle>:S`n}" using n(2) apply_equality[OF _ z] by auto
  }
  then have "{n:I. y`n\<in>S1`n} \<subseteq> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n}" by auto
  moreover have "\<forall>C\<in>Pow(I). {n:I. y`n\<in>S1`n} \<subseteq> C \<longrightarrow> C \<in> \<FF>"
    using ultraFilter x(3) unfolding IsFilter_def IsUltrafilter_def by auto
  then have "{n:I.  \<langle>y`n, ?z`n\<rangle>:S`n}:Pow(I) \<longrightarrow> ({n:I. y`n\<in>S1`n} \<subseteq> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<longrightarrow> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<in> \<FF>)"
    unfolding Ball_def by auto
  then have "{n:I. y`n\<in>S1`n} \<subseteq> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<longrightarrow> {n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<in> \<FF>" by auto
  ultimately have "{n:I.  \<langle>y`n, ?z`n\<rangle>:S`n} \<in> \<FF>" by auto
  then have "\<langle>hyper_rel``{y},hyper_rel``{?z}\<rangle>\<in>internal_fun(S)"
    using z x(2,3) unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] by auto
  then show "x\<in>domain(internal_fun(S))" using x(1) unfolding domain_def by auto
next
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  fix x y z assume as:"\<langle>x,y\<rangle>\<in>internal_fun(S)" "\<langle>x,z\<rangle>\<in>internal_fun(S)"
  from as(1) obtain h j where f:"x= hyper_rel``{h}" "y=hyper_rel``{j}" "h:Pi(I,X)" "j:Pi(I,X)" "{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<in>\<FF>"
    unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] by auto
  from as(2) obtain k m where g:"x=hyper_rel``{m}" "z=hyper_rel``{k}" "m:Pi(I,X)" "k:Pi(I,X)" "{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n}\<in>\<FF>"
    unfolding internal_fun_def[OF assms] internal_rel_def[OF SS] using f(1) by auto
  from f(1) g(1) have "hyper_rel``{h} = hyper_rel``{m}" by auto
  then have "\<langle>h,m\<rangle>\<in>hyper_rel" using same_image_equiv[OF hyper_equiv] g(3) by auto
  then have "{n:I. h`n = m`n}:\<FF>" unfolding hyper_rel_def by auto
  with f(5) have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  with g(5) have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<forall>A\<in>Pow(I). {n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> A \<longrightarrow> A\<in>\<FF>" 
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then have "{n:I. j`n=k`n}:Pow(I) \<Longrightarrow> {n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> {n:I. j`n=k`n} \<longrightarrow> {n:I. j`n=k`n}\<in>\<FF>"
    by auto
  then have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> {n:I. j`n=k`n} \<longrightarrow> {n:I. j`n=k`n}\<in>\<FF>" by auto moreover
  {
    fix n assume "n:{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n}"
    then have n:"n\<in>I" "h`n=m`n" "\<langle>h`n, j`n\<rangle>:S`n" "\<langle>m`n, k`n\<rangle>:S`n" by auto
    with apply_type[OF assms(3) n(1)] have "j`n=k`n" unfolding Pi_def function_def by force
    with n(1) have "n:{n:I. j`n=k`n}" by auto
  }
  then have "{n:I. h`n = m`n}\<inter>{n\<in>I. \<langle>h`n, j`n\<rangle>:S`n}\<inter>{n\<in>I. \<langle>m`n, k`n\<rangle>:S`n} \<subseteq> {n:I. j`n=k`n}" by auto
  ultimately have "{n:I. j`n=k`n}\<in>\<FF>" by auto
  with f(4) g(4) have "\<langle>j,k\<rangle>\<in>hyper_rel" unfolding hyper_rel_def by auto
  with f(2) g(2) show "y=z" using equiv_class_eq[OF hyper_equiv] by auto
qed

lemma internal_fun_apply:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)" 
    and "x\<in>Pi(I,X)" "{i:I. x`i\<in>S1`i}\<in>\<FF>" (*[x]\<in>internal_set(S1)*)
  shows "internal_fun(S)`(hyper_rel``{x}) = hyper_rel``{{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}}"
    and "{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}:Pi(I,X)"
proof- 
  have SS:"S:Pi(I, \<lambda>i. Pow(X(i)\<times>X(i)))"
  proof-
    {
      fix x assume "x\<in>S"
      with assms(3) have "x\<in>(\<Sum>i\<in>I. S1`i \<rightarrow> S2`i)" unfolding Pi_def by auto
      then obtain i f where f:"x=\<langle>i,f\<rangle>" "i\<in>I" "f\<in>S1`i \<rightarrow> S2`i" by auto
      from f(3) have "f \<subseteq> S1`i\<times>S2`i" unfolding Pi_def by auto
      then have "f \<subseteq> X(i)\<times>X(i)" using apply_type[OF assms(1) f(2)] apply_type[OF assms(2) f(2)] by auto
      with f(1,2) have "x\<in>(\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    }
    then have "S \<subseteq> (\<Sum>i\<in>I. Pow(X(i)\<times>X(i)))" by auto
    then show ?thesis using assms(3) unfolding Pi_def by auto
  qed
  let ?z="{\<langle>i, if x`i\<in>S1`i then (S`i)`(x`i) else x`i\<rangle>. i\<in>I}"
  show z:"?z\<in>Pi(I,X)" unfolding Pi_def function_def apply auto prefer 2
    using assms(4) apply_type apply simp
  proof-
    fix i assume i:"i:I" "x ` i \<in> S1 ` i"
    from i(1) assms(3) have "S`i:S1`i \<rightarrow> S2`i" using apply_type by auto
    with i(2) have "(S`i)`(x`i):S2`i" using apply_type by auto
    with i(1) show "(S`i)`(x`i):X(i)" using apply_type[OF assms(2)] by auto
  qed
  have "hyper_rel``{x}\<in>internal_set(S1)" unfolding internal_set_def[OF assms(1)]
    using assms(4,5) by auto
  then have "\<langle>hyper_rel``{x},internal_fun(S)`(hyper_rel``{x})\<rangle>\<in>internal_fun(S)"
    using apply_Pair internal_fun_is_fun[OF assms(1-3)] by auto
  then have "\<langle>hyper_rel``{x},internal_fun(S)`(hyper_rel``{x})\<rangle>\<in>{\<langle>hyper_rel``{x},hyper_rel``{y}\<rangle>.
    \<langle>x,y\<rangle> \<in> {\<langle>p,q\<rangle> \<in> (\<Prod>i\<in>I. X(i)) \<times> (\<Prod>i\<in>I. X(i)) . {n \<in> I . \<langle>p ` n, q ` n\<rangle> \<in> S ` n} \<in> \<FF>}}"
    unfolding internal_fun_def[OF assms(1-3)] internal_rel_def[OF SS] by auto
  then obtain t y where A:"hyper_rel``{x}=hyper_rel``{t}" "internal_fun(S)`(hyper_rel``{x}) = hyper_rel``{y}"
    "t:Pi(I,X)" "y:Pi(I,X)" "{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n} \<in> \<FF>" by auto
  from A(1,3) assms(4) have "\<langle>x,t\<rangle>\<in>hyper_rel" using eq_equiv_class hyper_equiv by auto
  then have "{i:I. x`i = t`i}:\<FF>" unfolding hyper_rel_def by auto
  with A(5) have "{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n}:\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto moreover
  have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}\<in>Pow(I)" by auto
  ultimately have "{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n} \<longrightarrow> {n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
  {
    fix i assume "i\<in>{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n}"
    then have "i: I" "x`i=t`i" "\<langle>t ` i, y ` i\<rangle> \<in> S ` i" by auto
    then have "i:I" "\<langle>x`i,y`i\<rangle>\<in>S`i" by auto
    then have "i\<in>{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}" by auto
  }
  then have "{i:I. x`i = t`i}\<inter>{n \<in> I . \<langle>t ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}" by auto
  ultimately have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}:\<FF>" by auto
  moreover have "{n\<in>I. ?z`n = y`n}\<in>Pow(I)" by auto
  ultimately have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n\<in>I. ?z`n = y`n} \<longrightarrow> {n\<in>I. ?z`n = y`n}\<in>\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto moreover
  {
    fix n assume "n:{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n}"
    then have n:"n\<in>I" "\<langle>x`n,y`n\<rangle>\<in>S`n" by auto
    from n(1) have "S`n:S1`n\<rightarrow>S2`n" using apply_type[OF assms(3)] by auto
    with n(2) have "\<langle>x`n,y`n\<rangle>\<in>S`n" "x`n\<in>S1`n" "(S`n)`(x`n) = y`n"
      using apply_equality[of "x`n" "y`n" "S`n" "S1`n" "\<lambda>_. S2`n"] unfolding Pi_def by auto
    then have "(if x`n\<in>S1`n then (S`n)`(x`n) else x`n) = y`n" by auto
    with n(1) have "n\<in>{n\<in>I. ?z`n = y`n}" using apply_equality z by auto
  }
  then have "{n \<in> I . \<langle>x ` n, y ` n\<rangle> \<in> S ` n} \<subseteq> {n\<in>I. ?z`n = y`n}" by auto
  ultimately have "{n\<in>I. ?z`n = y`n}\<in>\<FF>" by auto
  then have "\<langle>?z,y\<rangle>\<in>hyper_rel" unfolding hyper_rel_def using A(4) z by auto
  then have "\<langle>y,?z\<rangle>\<in>hyper_rel" using hyper_sym unfolding sym_def by auto
  then have "hyper_rel``{y} = hyper_rel``{?z}" using equiv_class_eq[OF hyper_equiv]
    by auto
  with A(2) show "internal_fun(S)`(hyper_rel``{x}) = hyper_rel``{{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}}" by auto
qed

lemma internal_fun_apply_2:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)" 
    and "hyper_rel``{x}\<in>internal_set(S1)"
  shows "internal_fun(S)`(hyper_rel``{x}) = hyper_rel``{{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}}"
    and "{\<langle>i, if x ` i \<in> S1 ` i then S ` i ` (x ` i) else x ` i\<rangle> . i \<in> I}:Pi(I,X)"
  apply (rule internal_fun_apply) using assms(1) apply simp using assms(2) apply simp
  using assms(3) apply simp prefer 3 apply (rule internal_fun_apply)
  using assms(1) apply simp using assms(2) apply simp
  using assms(3) apply simp 
proof-
  from assms(4) obtain y where A:"hyper_rel``{x} = hyper_rel``{y}" "y:Pi(I,X)" "{n\<in>I. y`n\<in>S1`n}\<in>\<FF>"
    unfolding internal_set_def[OF assms(1)] by auto
  from eq_equiv_class[OF A(1) hyper_equiv A(2)] show "x:Pi(I,X)" unfolding hyper_rel_def by auto
  then show "x\<in>Pi(I,X)" by auto
  from eq_equiv_class[OF A(1) hyper_equiv A(2)] have "{n\<in>I. x`n = y`n}:\<FF>" unfolding hyper_rel_def by auto
  with A(3) have "{n\<in>I. x`n = y`n} \<inter>{n\<in>I. y`n\<in>S1`n}\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  moreover have "{n\<in>I. x`n\<in>S1`n}\<in>Pow(I)" by auto
  ultimately have "{n\<in>I. x`n = y`n} \<inter>{n\<in>I. y`n\<in>S1`n} \<subseteq> {n\<in>I. x`n\<in>S1`n} \<longrightarrow> {n\<in>I. x`n\<in>S1`n}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  then show "{n\<in>I. x`n\<in>S1`n}:\<FF>" by auto
  then show "{n\<in>I. x`n\<in>S1`n}:\<FF>" by auto
qed
  
lemma internal_fun_inj:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)" 
    and "{i:I. S`i:inj(S1`i,S2`i)}\<in>\<FF>"
  shows "internal_fun(S)\<in>inj(internal_set(S1), internal_set(S2))"
  unfolding inj_def
proof(safe)
  from internal_fun_is_fun[OF assms(1-3)] show "internal_fun(S) \<in> internal_set(S1) \<rightarrow> internal_set(S2)" by auto
  fix w x assume as:"x\<in>internal_set(S1)" "w\<in>internal_set(S1)" "internal_fun(S)`w = internal_fun(S)`x"
  from as(1,2) obtain xx wx where p:"xx:Pi(I,X)" "wx\<in>Pi(I,X)" "{i\<in>I. xx`i \<in>S1`i}\<in>\<FF>"  "{i\<in>I. wx`i \<in>S1`i}\<in>\<FF>"
    "x=hyper_rel``{xx}" "w=hyper_rel``{wx}"
    unfolding internal_set_def[OF assms(1)] by auto
  from as have ap:"hyper_rel ``
    {{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}} =
hyper_rel `` {{\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}}" using internal_fun_apply_2[OF assms(1-3)] p(5,6)
    by auto moreover
  have ff:"{\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}\<in>Pi(I,X)"
    "{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}\<in>Pi(I,X)"
    using apply_type[OF assms(1)] apply_type[OF apply_type[OF assms(3)]] unfolding Pi_def function_def
    apply auto prefer 2 using apply_type[OF p(2)] apply simp
    using apply_type[OF assms(2)] apply blast
     prefer 2 using apply_type[OF p(1)] apply simp
    using apply_type[OF assms(2)] by blast
  ultimately have "\<langle>{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}, {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}\<rangle>\<in>hyper_rel"
    using eq_equiv_class[OF _ hyper_equiv, of "{\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}" "{\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}"]
    by auto
  then have Q:"{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<in>\<FF>"
    unfolding hyper_rel_def by auto
  have R:"\<And>x y. x\<in>\<FF> \<Longrightarrow> y\<in>\<FF> \<Longrightarrow> x\<inter>y\<in>\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  from p(3,4) have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<in>\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<And>Q. Q:\<FF> \<Longrightarrow> {i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>Q\<in>\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  with Q have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<in>\<FF>"
    by auto
  with assms(4) R have "({i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i})\<inter>{i \<in> I . S ` i \<in> inj(S1 ` i, S2 ` i)}:\<FF>"
    by auto
  then have "\<And>Q. Q\<in>Pow(I) \<Longrightarrow> {i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> I . S ` i \<in> inj(S1 ` i, S2 ` i)} \<subseteq> Q \<Longrightarrow> Q:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
  {
    fix i assume "i\<in>{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> I . S ` i \<in> inj(S1 ` i, S2 ` i)}"
    then have i:"i\<in>I" "xx`i\<in>S1`i" "wx`i\<in>S1`i" "S ` i ` (xx ` i) = S ` i ` (wx ` i)" "S`i\<in>inj(S1`i,S2`i)" using apply_equality ff by auto
    from i(2-5) have "xx`i = wx`i" unfolding inj_def by auto
    with i(1) have "i\<in>{i\<in>I. xx`i = wx`i}" by auto
  }
  then have "{i\<in>I. xx`i \<in>S1`i}\<inter>{i\<in>I. wx`i \<in>S1`i}\<inter>{i\<in>I. {\<langle>i, if xx ` i \<in> S1 ` i then S ` i ` (xx ` i) else xx ` i\<rangle> . i \<in> I}`i = {\<langle>i, if wx ` i \<in> S1 ` i then S ` i ` (wx ` i) else wx ` i\<rangle> . i \<in> I}`i}\<inter>{i \<in> I . S ` i \<in> inj(S1 ` i, S2 ` i)} \<subseteq> {i\<in>I. xx`i = wx`i}" by auto
  moreover have "{i\<in>I. xx`i = wx`i}\<in>Pow(I)" by auto
  ultimately have "{i\<in>I. xx`i = wx`i}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
    by auto
  then have "\<langle>xx,wx\<rangle>\<in>hyper_rel" unfolding hyper_rel_def using p(1,2) by auto
  then show "w = x" using equiv_class_eq[OF hyper_equiv, THEN sym] p(5,6) by auto
qed

lemma internal_inj_fun:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)"
    and "internal_fun(S)\<in>inj(internal_set(S1), internal_set(S2))"
    and "Pi({n\<in>I. S`n\<notin>inj(S1`n,S2`n)},\<lambda>n. {\<langle>q1,q2\<rangle>\<in>S1`n\<times>S1`n. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2})\<noteq>0"
    and "Pi(I,X)\<noteq>0"
  shows "{n\<in>I. S`n\<in>inj(S1`n,S2`n)}\<in>\<FF>"
proof-
  {
    assume "I-{n\<in>I. S`n\<in>inj(S1`n,S2`n)}\<in>\<FF>"
    moreover have "I-{n\<in>I. S`n\<in>inj(S1`n,S2`n)} = {n\<in>I. S`n\<notin>inj(S1`n,S2`n)}" by auto
    ultimately have B:"{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}\<in>\<FF>" by auto
    from assms(5) obtain q where q:"q\<in>Pi({n\<in>I. S`n\<notin>inj(S1`n,S2`n)},\<lambda>n. {\<langle>q1,q2\<rangle>\<in>S1`n\<times>S1`n. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2})"
      by auto
    from assms(6) obtain x where x:"x\<in>Pi(I,X)" by auto
    let ?x="{\<langle>n,if S`n\<notin>inj(S1`n,S2`n) then fst(q`n) else x`n\<rangle>. n\<in>I}"
    let ?y="{\<langle>n,if S`n\<notin>inj(S1`n,S2`n) then snd(q`n) else x`n\<rangle>. n\<in>I}"
    have fun:"?x\<in>Pi(I,X)" "?y\<in>Pi(I,X)" unfolding Pi_def function_def apply auto
      prefer 2 using apply_type[OF x] apply simp
        prefer 3 using apply_type[OF x] apply simp
    proof-
      fix n assume ni:"n\<in>I" "S ` n \<notin> inj(S1 ` n, S2 ` n)"
      then have "q`n\<in>{\<langle>q1,q2\<rangle>\<in>S1`n\<times>S1`n. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2}"
        using apply_type[OF q] by auto
      then have A:"fst(q`n)\<in>S1`n" "snd(q`n)\<in>S1`n" by auto
      from A(1) show "fst(q`n)\<in>X(n)" using apply_type[OF assms(1)] ni(1) by auto
      from A(2) show "snd(q`n)\<in>X(n)" using apply_type[OF assms(1)] ni(1) by auto
    qed
    {
      fix n assume n1:"n\<in>{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}"
      then have n:"n\<in>I" "S`n\<notin>inj(S1`n,S2`n)" by auto
      have "q`n\<in>{\<langle>q1,q2\<rangle>\<in>S1`n\<times>S1`n. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2}"
        using apply_type[OF q n1] by auto
      then obtain qx qy where qq:"q`n = \<langle>qx,qy\<rangle>" "qx:S1`n" "qy:S1`n" "(S`n)`qx = (S`n)`qy" "qx\<noteq>qy" by auto
      from fun have "?x`n=qx" "?y`n=qy" using n(2) qq(1) apply_equality[of _ _ ?x] apply_equality[of _ _ ?y]
        n(1) by auto
      with qq(1-3) have "?x`n:S1`n" "?y`n:S1`n" by auto
      with n(1) have "n\<in>{n\<in>I. ?x`n:S1`n}" "n\<in>{n\<in>I. ?y`n:S1`n}" by auto
    }
    then have "{n\<in>I. S`n\<notin>inj(S1`n,S2`n)} \<subseteq> {n\<in>I. ?x`n:S1`n}" "{n\<in>I. S`n\<notin>inj(S1`n,S2`n)} \<subseteq> {n\<in>I. ?y`n:S1`n}" by auto
    moreover note B moreover have "{n\<in>I. ?x`n:S1`n}:Pow(I)"  "{n\<in>I. ?y`n:S1`n}:Pow(I)" by auto
    ultimately have C:"{n\<in>I. ?x`n:S1`n}\<in>\<FF>" "{n\<in>I. ?y`n:S1`n}\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have el:"hyper_rel``{?x}\<in>internal_set(S1)" "hyper_rel``{?y}\<in>internal_set(S1)"
      using fun unfolding internal_set_def[OF assms(1)] by auto
    then have els:"internal_fun(S)`(hyper_rel``{?x}) = hyper_rel``{{\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}}"
      "internal_fun(S)`(hyper_rel``{?y}) = hyper_rel``{{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}}"
      using internal_fun_apply_2[OF assms(1-3)] by auto
    moreover from C have "{n\<in>I. ?x`n:S1`n}\<inter>{n\<in>I. ?y`n:S1`n}\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    with B have D:"{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}\<inter>({n\<in>I. ?x`n:S1`n}\<inter>{n\<in>I. ?y`n:S1`n})\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    from el have fun_els:"{\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}\<in>Pi(I,X)" 
       "{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}\<in>Pi(I,X)" 
       using internal_fun_apply_2[OF assms(1-3)] by auto
    {
      fix n assume n1:"n\<in>{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}\<inter>{n\<in>I. ?x`n:S1`n}\<inter>{n\<in>I. ?y`n:S1`n}"
      then have n:"n:I" "?x`n:S1`n" "?y`n:S1`n" "S`n\<notin>inj(S1`n,S2`n)" by auto
      then have R:"{\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}`n = S ` n ` (?x ` n)"
        "{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`n = S ` n ` (?y ` n)"
        using apply_equality fun_els by auto
      have "q`n\<in>{\<langle>q1,q2\<rangle>\<in>S1`n\<times>S1`n. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2}"
        using apply_type[OF q] n(1,4) by auto
      then obtain qx qy where qq:"q`n = \<langle>qx,qy\<rangle>" "qx:S1`n" "qy:S1`n" "(S`n)`qx = (S`n)`qy" "qx\<noteq>qy" by auto
      from fun have "?x`n=qx" "?y`n=qy" using n(2,3) qq(1) apply_equality[of _ _ ?x] apply_equality[of _ _ ?y]
        n(1,4) by auto
      with R n(2,3) qq(4,5) have "{\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}`n =
        {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`n" by auto
      with n(1) have "n:{n\<in>I. {\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}`n =
        {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`n}" by auto
    }
    then have "{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}\<inter>({n\<in>I. ?x`n:S1`n}\<inter>{n\<in>I. ?y`n:S1`n}) \<subseteq> {n\<in>I. {\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}`n =
        {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`n}" by auto
    moreover have "{n\<in>I. {\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}`n =
        {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`n}\<in>Pow(I)" by auto
    moreover note D ultimately have "{n\<in>I. {\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}`n =
        {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`n}\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<langle>{\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I},{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}\<rangle>\<in>hyper_rel"
      using fun_els unfolding hyper_rel_def by auto
    then have "hyper_rel``{{\<langle>i, if ?x ` i \<in> S1 ` i then S ` i ` (?x ` i) else ?x ` i\<rangle> . i \<in> I}} =
      hyper_rel``{{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}}"
      using equiv_class_eq[OF hyper_equiv] by auto
    with els have "internal_fun(S)`(hyper_rel``{?x}) = internal_fun(S)`(hyper_rel``{?y})"
      by auto
    then have "hyper_rel``{?x} = hyper_rel``{?y}" using assms(4)
      unfolding inj_def[of "internal_set(S1)" "internal_set(S2)"] using el
      by auto
    then have "\<langle>?x,?y\<rangle>\<in>hyper_rel" using eq_equiv_class[OF _ hyper_equiv] fun by auto
    then have "{n\<in>I. ?x`n = ?y`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with B have "{n\<in>I. ?x`n = ?y`n}\<inter>{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix n assume "n\<in>{n\<in>I. ?x`n = ?y`n}\<inter>{n\<in>I. S`n\<notin>inj(S1`n,S2`n)}"
       then have n:"n\<in>I" "S`n\<notin>inj(S1`n,S2`n)" "?x`n =?y`n" by auto
      have "q`n\<in>{\<langle>q1,q2\<rangle>\<in>S1`n\<times>S1`n. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2}"
        using apply_type[OF q] n by auto
      then obtain qx qy where qq:"q`n = \<langle>qx,qy\<rangle>" "qx:S1`n" "qy:S1`n" "(S`n)`qx = (S`n)`qy" "qx\<noteq>qy" by auto
      from fun have "?x`n=qx" "?y`n=qy" using n(2) qq(1) apply_equality[of _ _ ?x] apply_equality[of _ _ ?y]
        n(1) by auto
      with qq(5) n(3) have False by auto
    }
    then have "{n\<in>I. ?x`n = ?y`n}\<inter>{n\<in>I. S`n\<notin>inj(S1`n,S2`n)} = 0" by auto
    ultimately have "0:\<FF>" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then show "{n \<in> I . S ` n \<in> inj(S1 ` n, S2 ` n)} \<in> \<FF>"
    using set_ultrafilter[OF _ ultraFilter] by auto
qed


lemma internal_fun_converse:
  assumes "S1 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S2 \<in> (\<Prod>i\<in>I. Pow(X(i)))" "S \<in> (\<Prod>i\<in>I. S1 ` i \<rightarrow> S2 ` i)"
    and "internal_fun(S)\<in>bij(internal_set(S1), B)" and "(\<Prod>n\<in>{n \<in> I . S ` n \<notin> inj(S1 ` n, S2 ` n)}.
      {\<langle>q1,q2\<rangle> \<in> S1 ` n \<times> S1 ` n . S ` n ` q1 = S ` n ` q2 \<and> q1 \<noteq> q2}) \<noteq> 0"
  defines "SS \<equiv> {\<langle>i, if S`i\<in>inj(S1`i,S2`i) then converse(S`i) else 0\<rangle>. i\<in>I}"
  shows "converse(internal_fun(S)) = internal_fun(SS)"
  apply(rule fun_extension[of "converse(internal_fun(S))" B "\<lambda>_. internal_set(S1)" 
      "internal_fun(SS)" "\<lambda>_. internal_set(S1)"])
proof-
  let ?S1'= "{\<langle>i,if S`i\<in>inj(S1`i,S2`i) then S1`i else 0\<rangle>. i\<in>I}"
  let ?S2'= "{\<langle>i,if S`i\<in>inj(S1`i,S2`i) then S2`i else 0\<rangle>. i\<in>I}"
  let ?S' = "{\<langle>i, if S`i\<in>inj(S1`i,S2`i) then S`i else 0\<rangle>. i\<in>I}"
  from assms(4) have "converse(internal_fun(S))\<in>bij(B,internal_set(S1))"
    using bij_converse_bij by auto
  then show CC:"converse(internal_fun(S)):B \<rightarrow> internal_set(S1)" using bij_is_fun by auto
  from internal_fun_is_fun[OF assms(1-3)] have F:"internal_fun(S):internal_set(S1)\<rightarrow>internal_set(S2)"
    by auto
  then have INJ:"internal_fun(S)\<in>inj(internal_set(S1),internal_set(S2))"
    using bij_is_inj[OF assms(4)] unfolding inj_def by auto
  have S1:"?S1'\<in>(\<Prod>i\<in>I. Pow(X(i)))" unfolding Pi_def function_def apply auto
    using if_iff apply auto using apply_type[OF assms(1)] by auto
  have S2:"?S2'\<in>(\<Prod>i\<in>I. Pow(X(i)))" unfolding Pi_def function_def apply auto
    using if_iff apply auto using apply_type[OF assms(2)] by auto
  have S:"?S'\<in>(\<Prod>i\<in>I. ?S1'`i \<rightarrow> ?S2'`i)" unfolding Pi_def
    function_def apply auto
  proof-
    {
      fix i x assume as:"i\<in>I" "x \<in> (if S ` i \<in> inj(S1 ` i, S2 ` i) then S ` i else 0)"
      {
        assume A:"S ` i \<in> inj(S1 ` i, S2 ` i)"
        with as(2) have "x\<in>S`i" by auto moreover
        from A have "?S1'`i =S1`i" using apply_equality[OF _ S1] as(1) by auto
        moreover from A have "?S2'`i =S2`i" using apply_equality[OF _ S2] as(1) by auto
        moreover from as(1) have "S`i:S1`i\<rightarrow>S2`i" using apply_type[OF assms(3)] by auto
        ultimately have "x\<in>?S1'`i\<times>?S2'`i" unfolding Pi_def by auto
      } moreover
      {
        assume A:"S`i\<notin>inj(S1 ` i, S2 ` i)"
        with as(2) have False by auto
      }
      ultimately show "x\<in>?S1'`i\<times>?S2'`i" by auto
    }
    {
      fix i x assume as:"i \<in> I" "x \<in> ?S1' ` i" "S ` i \<in> inj(S1 ` i, S2 ` i)"
      from as(3) have "?S1'`i =S1`i" using apply_equality[OF _ S1] as(1) by auto
      with as(2) show "x\<in>domain(S`i)" using apply_type[OF assms(3)] as(1) unfolding Pi_def by auto
    }
    {
      fix i x assume as:"i \<in> I" "x \<in> ?S1' ` i" 
      {
        assume A:"S ` i \<notin> inj(S1 ` i, S2 ` i)"
        from A have "?S1'`i = 0" using apply_equality[OF _ S1] as(1) by auto
        with as have False by auto
      }
      then show "S ` i \<in> inj(S1 ` i, S2 ` i)" by auto
    }
    {
      fix i x y y' assume as:"i \<in> I"
       "\<langle>x, y\<rangle> \<in> (if S ` i \<in> inj(S1 ` i, S2 ` i) then S ` i else 0)"
       "\<langle>x, y'\<rangle> \<in> (if S ` i \<in> inj(S1 ` i, S2 ` i) then S ` i else 0)"
      {
        assume A:"S ` i \<notin> inj(S1 ` i, S2 ` i)"
        with as(2) have False by auto
      }
      then have inj:"S`i\<in>inj(S1 ` i, S2 ` i)" by auto
      then have "S`i:S1`i \<rightarrow> S2`i" unfolding inj_def by auto moreover
      from inj as(2,3) have "\<langle>x,y\<rangle>\<in>S`i" "\<langle>x,y'\<rangle>\<in>S`i" by auto
      ultimately show "y=y'" unfolding Pi_def function_def by blast
    }
  qed
  let ?S2="{\<langle>i, range(?S' ` i)\<rangle>. i\<in>I}"
  {
    fix i assume i:"i\<in>I"
    then have "?S'`i:?S1'`i \<rightarrow> ?S2'`i" using apply_type[OF S] by auto
    then have "range(?S'`i) \<subseteq> ?S2'`i" using func1_1_L5B by auto
    then have "range(?S'`i) \<subseteq> X(i)" using apply_type[OF S2 i] by auto
  }
  then have SS2:"?S2\<in>(\<Prod>i\<in>I. Pow(X(i)))" unfolding Pi_def function_def by auto
  have SS:"SS\<in>(\<Prod>i\<in>I. range(?S'`i) \<rightarrow> S1`i)" unfolding SS_def Pi_def
    function_def apply auto
  proof-
    {
      fix i x assume as:"i \<in> I"
       "x \<in> (if S ` i \<in> inj(S1 ` i, S2 ` i) then converse(S ` i) else 0)"
      {
        assume A:"S ` i \<in> inj(S1 ` i, S2 ` i)"
        with as(2) have "x:converse(S`i)" by auto
        then obtain x1 x2 where x:"\<langle>x2,x1\<rangle>\<in>S`i" "x=\<langle>x1,x2\<rangle>" unfolding converse_def by auto
        from as(1) have "S`i:S1`i\<rightarrow>S2`i" using apply_type[OF assms(3)] by auto
        then have "S`i:S1`i\<rightarrow>range(S`i)" using range_of_fun by auto
        with x(1) have "x2\<in>S1`i" "x1\<in>range(S`i)" unfolding Pi_def by auto
        with x(2) have "x\<in>range(S`i)\<times>S1`i" by auto
        moreover have "?S'`i = S`i" using apply_equality[OF _ S, of i] as(1) A
          by auto
        ultimately have "x \<in> range(?S' ` i) \<times> S1 ` i" by auto
      }moreover
      {
        assume A:"S ` i \<notin> inj(S1 ` i, S2 ` i)"
        with as(2) have False by auto
      } ultimately
      show "x\<in>range(?S'`i)\<times>S1`i" by auto
    }
    {
      fix i x y assume as:"i \<in> I" "\<langle>x, y\<rangle> \<in> ?S' ` i" "S ` i \<in> inj(S1 ` i, S2 ` i)"
      from as(1,3) have "?S' `i = S`i" using apply_equality[OF _ S, of i] as(1)
        by auto
      with as(2) have "\<langle>x,y\<rangle>\<in>S`i" by auto
      then show "y\<in>range(S`i)" using rangeI by auto
    }
    {
      fix i x y assume as:"i \<in> I" "\<langle>x, y\<rangle> \<in> ?S' ` i"
      {
        assume A:"S ` i \<notin> inj(S1 ` i, S2 ` i)"
        with as(1,2) have False using apply_equality[OF _ S] by auto
      }
      then show "S`i:inj(S1 ` i, S2 ` i)" by auto
    }
    {
      fix i xa y y' assume as:"i \<in> I"
       "\<langle>xa, y\<rangle> \<in> (if S ` i \<in> inj(S1 ` i, S2 ` i) then converse(S ` i) else 0)"
       "\<langle>xa, y'\<rangle> \<in> (if S ` i \<in> inj(S1 ` i, S2 ` i) then converse(S ` i) else 0)"
      {
        assume A:"S ` i \<notin> inj(S1 ` i, S2 ` i)"
        with as(1,2) have False using apply_equality[OF _ S] by auto
      }
      then have A:"S`i:inj(S1 ` i, S2 ` i)" by auto
      with as(2,3) have "\<langle>xa,y\<rangle>\<in>converse(S`i)" "\<langle>xa,y'\<rangle>\<in>converse(S`i)" by auto
      then have "\<langle>y,xa\<rangle>:S`i" "\<langle>y',xa\<rangle>:S`i" unfolding converse_def by auto
      moreover then have "y\<in>S1`i" "y'\<in>S1`i" "(S`i)`y=xa" "(S`i)`y'=xa" using apply_type[OF assms(3) as(1)]
        unfolding Pi_def using apply_equality[OF _ inj_is_fun[OF A]] by auto moreover note A
      ultimately show "y=y'" unfolding inj_def by auto
    }
  qed
  then have T:"SS \<in> (\<Prod>i\<in>I. {\<langle>i, range(?S' ` i)\<rangle> . i \<in> I} ` i \<rightarrow> S1 ` i)"
    using apply_equality[OF _ SS2] unfolding Pi_def Sigma_def by auto
  from internal_fun_is_fun(1)[OF SS2 assms(1) this]
  have Q:"internal_fun(SS) \<in>
  internal_set({\<langle>i, range(?S' ` i)\<rangle> . i \<in> I}) \<rightarrow> internal_set(S1)" by auto
  {
    fix t assume "t\<in>internal_set({\<langle>i, range(?S' ` i)\<rangle> . i \<in> I})"
    then obtain x where x:"t=hyper_rel``{x}" "x\<in>Pi(I,X)" "{n\<in>I. x`n\<in>{\<langle>i, range(?S' ` i)\<rangle> . i \<in> I}`n}:\<FF>"
      unfolding internal_set_def[OF SS2] by auto
    from x(3) have P:"{n\<in>I. x`n\<in>range(?S' ` n)}:\<FF>" using apply_equality[OF _ SS2]
      by auto
    let ?y="{\<langle>n,if S`n\<in>inj(S1`n,S2`n) \<and> x`n\<in>range(S`n) then (converse(S`n)`(x`n)) else x`n\<rangle>. n\<in>I}"
    have Y:"?y\<in>Pi(I,X)" unfolding Pi_def function_def apply auto
      prefer 2 using apply_type[OF x(2)] apply simp
      prefer 2 using apply_type[OF x(2)] apply simp
    proof-
      fix n xa assume n:"n:I" "S`n:inj(S1`n,S2`n)" "\<langle>xa, x ` n\<rangle> \<in> S ` n"
      from n(2) have "converse(S`n):range(S`n) \<rightarrow> S1`n" using inj_converse_fun by auto
      then have "converse(S`n)`(x`n) = xa" using apply_equality n(3) converse_iff[of "x`n" xa]
        by auto
      moreover from n(2,3) have "xa\<in>S1`n" unfolding inj_def Pi_def by auto
      then have "xa\<in>X(n)" using apply_type[OF assms(1)] n(1) by auto
      ultimately show "converse(S`n)`(x`n)\<in>X(n)" by auto
    qed
    {
      fix n assume "n\<in>{n\<in>I. x`n\<in>range(?S' ` n)}"
      then have n:"n:I" "x`n:range(?S'`n)" by auto
      from n(1) have "?S'`n:?S1'`n\<rightarrow>?S2'`n" using apply_type S by auto
      {
        assume "S`n\<notin>inj(S1`n,S2`n)"
        then have "?S'`n = 0" using apply_equality[OF _ S] n(1) by auto
        then have "range(?S'`n) = 0" by auto
        with n(2) have False by auto
      }
      then have Z:"S`n\<in>inj(S1`n,S2`n)" by auto
      then have "?S'`n = S`n" using n(1) apply_equality[OF _ S] by auto
      with n(2) have n2:"x`n:range(S`n)" by auto
      have "?y`n = (if (S ` n \<in> inj(S1 ` n, S2 ` n) \<and> x ` n \<in> range(S ` n)) then converse(S ` n) ` (x ` n)
         else (x ` n))" using apply_equality[of n, OF _ Y] n(1,2) by auto moreover
      from n2 Z have "S ` n \<in> inj(S1 ` n, S2 ` n) \<and> x ` n \<in> range(S ` n)" by blast ultimately
      have "?y`n = converse(S ` n) ` (x ` n)" by auto
      moreover from Z have "converse(S`n):range(S`n) \<rightarrow> S1`n" using inj_converse_fun by auto
      with n2 have "converse(S ` n) ` (x ` n):S1`n" using apply_type by auto
      ultimately have "?y`n:S1`n" by auto
      with n(1) have "n\<in>{n\<in>I. ?y`n:S1`n}" by auto
    }
    then have Q:"{n \<in> I . x ` n \<in> range(?S' ` n)} \<subseteq> {n\<in>I. ?y`n:S1`n}" by auto
    from P have "\<And>Q. Q\<in>Pow(I) \<Longrightarrow> {n \<in> I . x ` n \<in> range(?S' ` n)} \<subseteq> Q \<Longrightarrow> Q:\<FF>" using ultraFilter 
      unfolding IsFilter_def IsUltrafilter_def by auto moreover
    have "{n\<in>I. ?y`n:S1`n}:Pow(I)" by auto moreover note Q
    ultimately have B:"{n\<in>I. ?y`n:S1`n}:\<FF>" by auto
    with Y have M:"hyper_rel``{?y}\<in>internal_set(S1)" unfolding internal_set_def[OF assms(1)]
      by auto
    with internal_fun_apply_2[OF assms(1-3)] have A:"internal_fun(S) ` ((hyper_rel) `` {?y}) =
    hyper_rel ``
    {{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}}"
      "{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}:Pi(I,X)" by auto
    {
      fix t assume "t\<in>{n\<in>I. x`n\<in>range(?S' ` n)}\<inter>{n\<in>I. ?y`n:S1`n}"
      then have t:"t\<in>I" "x`t:range(?S'`t)" "?y`t:S1`t" by auto
      from A(2) t(1,3) have "{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t =
          (S ` t) ` (?y ` t)" using apply_equality by auto
      {
        assume "S`t\<notin>inj(S1`t,S2`t)"
        then have "?S'`t = 0" using apply_equality[OF _ S] t(1) by auto
        then have "range(?S'`t) = 0" by auto
        with t(2) have False by auto
      }
      then have Z:"S`t:inj(S1`t,S2`t)" by auto
      then have ZZ:"?S'`t = S`t" using apply_equality[OF _ S] t(1) by auto
      with Z t(1,2) have "?y`t = converse(S ` t) ` (x ` t)" using apply_equality[OF _ Y] by auto
      then have "{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t = (S`t)`(converse(S ` t) ` (x ` t))"
        using apply_equality[OF _ A(2)] t(1,3) by auto
      then have "{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t = x`t"
        using right_inverse[OF Z] t(2) ZZ by auto
      with t(1) have "t\<in>{t\<in>I. {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t = x`t}" by auto
    }
    then have "{n\<in>I. x`n\<in>range(?S' ` n)}\<inter>{n\<in>I. ?y`n:S1`n} \<subseteq> {t\<in>I. {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t = x`t}" by auto
    moreover have "{t\<in>I. {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t = x`t}:Pow(I)" by auto
    moreover from B P have "{n\<in>I. x`n\<in>range(?S' ` n)}\<inter>{n\<in>I. ?y`n:S1`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    ultimately have "{t\<in>I. {\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}`t = x`t}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    with A(2) x(2) have "\<langle>{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I},x\<rangle>\<in>hyper_rel"
      unfolding hyper_rel_def by auto
    then have "hyper_rel``{{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}} = hyper_rel``{x}"
      using equiv_class_eq[OF hyper_equiv] by auto
    with x(1) have "hyper_rel``{{\<langle>i, if ?y ` i \<in> S1 ` i then S ` i ` (?y ` i) else ?y ` i\<rangle> . i \<in> I}} = t" by auto
    with A(1) have "internal_fun(S)`(hyper_rel ``{?y}) = t" by auto
    then have "t\<in>range(internal_fun(S))" using apply_Pair[OF F M] rangeI by auto
    then have "t\<in>B" using surj_range[OF bij_is_surj[OF assms(4)]] by auto
  }
  then have A:"internal_set({\<langle>i, range(?S' ` i)\<rangle> . i \<in> I}) \<subseteq> B" by auto
  {
    fix t assume "t\<in>B"
    then have "t\<in>range(internal_fun(S))" using surj_range[OF bij_is_surj[OF assms(4)]] by auto
    then obtain q where q:"\<langle>q,t\<rangle>\<in>internal_fun(S)" using rangeE by auto
    then have q2:"internal_fun(S)`q = t" using apply_equality[OF _ bij_is_fun[OF assms(4)]] by auto
    from q have s:"q\<in>internal_set(S1)" "t\<in>internal_set(S2)" using bij_is_fun[OF assms(4)] F unfolding Pi_def by auto
    then obtain qx where x:"qx\<in>Pi(I,X)" "hyper_rel``{qx} = q" "{n\<in>I. qx`n\<in>S1`n}:\<FF>"
      unfolding internal_set_def[OF assms(1)] by auto
    from s x(2) have f:"internal_fun(S)`q = hyper_rel``{{\<langle>i,if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i\<rangle>. i\<in>I}}"
      "{\<langle>i,if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i\<rangle>. i\<in>I}:Pi(I,X)"
      using internal_fun_apply_2[OF assms(1-3), of qx] by auto
    from f(1) q2 have "hyper_rel``{{\<langle>i,if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i\<rangle>. i\<in>I}} = t" by auto
    moreover from s(2) obtain tx where xx:"tx:Pi(I,X)" "hyper_rel``{tx} = t" "{n\<in>I. tx`n\<in>S2`n}:\<FF>"
      unfolding internal_set_def[OF assms(2)] by auto
    note xx(2) ultimately have "\<langle>{\<langle>i,if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i\<rangle>. i\<in>I},tx\<rangle>\<in>hyper_rel"
      using eq_equiv_class[OF _ hyper_equiv xx(1)] by auto
    then have "{i\<in>I. {\<langle>i,if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i\<rangle>. i\<in>I}`i=tx`i}\<in>\<FF>"
      unfolding hyper_rel_def by auto
    then have "{i\<in>I. (if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i)=tx`i}\<in>\<FF>"
      using f(2) apply_equality by auto
    with x(3) have "{n\<in>I. qx`n\<in>S1`n}\<inter>{i\<in>I. (if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i)=tx`i}\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    from internal_inj_fun[OF assms(1-3) INJ assms(5)] xx(1) have 
      "{n \<in> I . S ` n \<in> inj(S1 ` n, S2 ` n)} \<in> \<FF>" by auto ultimately
    have "({n\<in>I. qx`n\<in>S1`n}\<inter>{i\<in>I. (if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i)=tx`i})\<inter>{n \<in> I . S ` n \<in> inj(S1 ` n, S2 ` n)} \<in> \<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix n assume "n\<in>{n\<in>I. qx`n\<in>S1`n}\<inter>{i\<in>I. (if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i)=tx`i}\<inter>{n \<in> I . S ` n \<in> inj(S1 ` n, S2 ` n)}"
      then have n1:"n\<in>I" "qx`n:S1`n" "(if qx ` n \<in> S1 ` n then S ` n ` (qx ` n) else qx ` n)=tx`n" "S`n\<in>inj(S1`n,S2`n)" by auto
      from n1(2,3) have "S ` n ` (qx ` n) = tx`n" by auto
      then have "tx`n \<in> range(S`n)" using rangeI[OF apply_Pair[OF apply_type[OF assms(3) n1(1)] n1(2)]] by auto
      then have "tx`n\<in>range(?S'`n)" using apply_equality[of n "S`n", OF _ S] using n1(1,4) by auto
      with n1(1) have "n\<in>{n\<in>I. tx`n\<in>range(?S'`n)}" by auto
      moreover have "{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`n = range(?S'`n)" using apply_equality[of n "range(?S'`n)" 
            "{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}" I "\<lambda>_. {range(?S'`i). i\<in>I}"] n1(1) unfolding Pi_def function_def
        by auto
      ultimately have "n\<in>{n\<in>I. tx`n\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`n}" by auto
    }
    then have "{n\<in>I. qx`n\<in>S1`n}\<inter>{i\<in>I. (if qx ` i \<in> S1 ` i then S ` i ` (qx ` i) else qx ` i)=tx`i}\<inter>{n \<in> I . S ` n \<in> inj(S1 ` n, S2 ` n)} \<subseteq> {n\<in>I. tx`n\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`n}" by auto
    moreover have "{n\<in>I. tx`n\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`n}:Pow(I)" by auto
    ultimately have "{n\<in>I. tx`n\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`n}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "hyper_rel``{tx}\<in>internal_set({\<langle>i,range(?S'`i)\<rangle>. i\<in>I})"
      unfolding internal_set_def[OF SS2] using xx(1) by auto
    with xx(2) have "t\<in>internal_set({\<langle>i,range(?S'`i)\<rangle>. i\<in>I})" by auto
  }
  then have "B \<subseteq> internal_set({\<langle>i,range(?S'`i)\<rangle>. i\<in>I})" by auto
  with A have eq:"B = internal_set({\<langle>i,range(?S'`i)\<rangle>. i\<in>I})" by auto
  from subst[OF this[THEN sym], of "\<lambda>B. internal_fun(SS) \<in> B \<rightarrow> internal_set(S1)"] Q 
  show "internal_fun(SS) \<in> B \<rightarrow> internal_set(S1)" by auto
  {
    fix x assume as:"x\<in>B"
    with eq have xx:"x\<in>internal_set({\<langle>i,range(?S'`i)\<rangle>. i\<in>I})" by auto
    then obtain xx where x:"xx\<in>Pi(I,X)" "x=hyper_rel``{xx}" "{i\<in>I. xx`i\<in>range(?S'`i)}:\<FF>"
      unfolding internal_set_def[OF SS2] using apply_equality[OF _ SS2] by auto
    have M:"internal_fun(SS)`x = hyper_rel``{{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}}"
      "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}:Pi(I,X)"
      using internal_fun_apply_2[OF SS2 assms(1) T, of xx] xx x(2) by auto
    have "internal_fun(S)`(converse(internal_fun(S))`x) = x"
      using right_inverse_lemma[OF F CC as] by auto 
    from as CC have A:"converse(internal_fun(S))`x :internal_set(S1)" using apply_type by auto
    then obtain yx where yx:"yx:Pi(I,X)" "converse(internal_fun(S))`x = hyper_rel``{yx}"
      "{i\<in>I. yx`i :S1`i}:\<FF>" unfolding internal_set_def[OF assms(1)] by auto
    from CC yx(2) have "\<langle>x, hyper_rel``{yx}\<rangle>\<in>converse(internal_fun(S))" 
      using apply_Pair[OF _ as, of "converse(internal_fun(S))" "\<lambda>_. internal_set(S1)"] by auto
    then have "\<langle>hyper_rel``{yx},x\<rangle>\<in>internal_fun(S)" using converse_iff by auto
    then have "internal_fun(S)`(hyper_rel``{yx}) = x" using apply_equality[OF _ F] by auto moreover
    have L:"internal_fun(S)`(hyper_rel``{yx}) = hyper_rel``{{\<langle>i, if yx`i\<in>S1`i then (S`i)`(yx`i) else yx`i\<rangle>. i\<in>I}}"
      "{\<langle>i, if yx`i\<in>S1`i then (S`i)`(yx`i) else yx`i\<rangle>. i\<in>I}\<in>Pi(I,X)"
      using internal_fun_apply_2[OF assms(1-3), of yx] A yx(2) by auto
    ultimately have "x = hyper_rel``{{\<langle>i, if yx`i\<in>S1`i then (S`i)`(yx`i) else yx`i\<rangle>. i\<in>I}}" by auto
    with x(1,2) have "\<langle>{\<langle>i, if yx`i\<in>S1`i then (S`i)`(yx`i) else yx`i\<rangle>. i\<in>I},xx\<rangle>\<in>hyper_rel"
      using eq_equiv_class[OF _ hyper_equiv, of _ xx] by auto
    then have "{n:I. {\<langle>i, if yx`i\<in>S1`i then (S`i)`(yx`i) else yx`i\<rangle>. i\<in>I}`n=xx`n}:\<FF>"
      unfolding hyper_rel_def by auto
    then have "{n:I. (if yx`n\<in>S1`n then (S`n)`(yx`n) else yx`n)=xx`n}:\<FF>"
      using apply_equality[OF _ L(2)] by auto
    with yx(3) have "{n:I. (if yx`n\<in>S1`n then (S`n)`(yx`n) else yx`n)=xx`n}\<inter>{n\<in>I. yx`n :S1`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix s assume "s\<in>{n:I. (if yx`n\<in>S1`n then (S`n)`(yx`n) else yx`n)=xx`n}\<inter>{n\<in>I. yx`n :S1`n}"
      then have s:"s\<in>I" "(if yx`s\<in>S1`s then (S`s)`(yx`s) else yx`s)=xx`s" "yx`s:S1`s" by auto
      then have "s\<in>I" "(S`s)`(yx`s)=xx`s" by auto
      then have "s\<in>I" "(SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s)" by auto
      with s(3) have "s\<in>{s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}" by auto
    }
    then have "{n:I. (if yx`n\<in>S1`n then (S`n)`(yx`n) else yx`n)=xx`n}\<inter>{n\<in>I. yx`n :S1`n} \<subseteq> {s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}" by auto
    moreover have "{s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}:Pow(I)" by auto
    ultimately have "{s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}\<inter>{i\<in>I. xx`i\<in>range(?S'`i)}:\<FF>"
      using x(3) ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix t assume "t\<in>{s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}\<inter>{i\<in>I. xx`i\<in>range(?S'`i)}"
      then have t:"t:I" "(SS`t)`((S`t)`(yx`t)) = (SS`t)`(xx`t)" "xx`t\<in>range(?S'`t)" "yx`t:S1`t" by auto
      {
        assume "S`t\<notin>inj(S1`t,S2`t)"
        then have "?S'`t = 0" using t(1) apply_equality[OF _ S] by auto
        then have "range(?S'`t) = 0" by auto
        with t(3) have False by auto
      }
      then have INJ:"S`t:inj(S1`t,S2`t)" by auto
      from M(2) have "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = (if xx`t\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`t then (SS`t)`(xx`t) else xx`t)"
        using apply_equality t(1) by auto
      then have "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = (if xx`t\<in>range(?S'`t) then (SS`t)`(xx`t) else xx`t)"
        using apply_equality[OF _ SS2] t(1) by auto
      then have "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = (SS`t)`(xx`t)"
        using t(3) by auto
      then have "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = (SS`t)`((S`t)`(yx`t))"
        using t(2) by auto
      then have "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = converse(S`t)`((S`t)`(yx`t))"
        using apply_equality[OF _ SS] t(1) INJ unfolding SS_def by auto
      then have "{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = yx`t" using left_inverse[OF INJ] t(4) by auto
      with t(1) have "t\<in>{t\<in>I. {\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = yx`t}" by auto
    }
    then have "{s\<in>I. (SS`s)`((S`s)`(yx`s)) = (SS`s)`(xx`s) \<and> yx`s\<in>S1`s}\<inter>{i\<in>I. xx`i\<in>range(?S'`i)} \<subseteq> {t\<in>I. {\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = yx`t}" by auto
    moreover have "{t\<in>I. {\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = yx`t}:Pow(I)" by auto
    ultimately have "{t\<in>I. {\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}`t = yx`t}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<langle>{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I},yx\<rangle>\<in>hyper_rel"
      using M(2) yx(1) unfolding hyper_rel_def by auto
    then have "hyper_rel``{{\<langle>i, if xx`i\<in>{\<langle>i,range(?S'`i)\<rangle>. i\<in>I}`i then (SS`i)`(xx`i) else xx`i\<rangle>. i\<in>I}} = hyper_rel``{yx}"
      using equiv_class_eq[OF hyper_equiv] by auto
    with M(1) have "internal_fun(SS)`x = hyper_rel``{yx}" by auto
    with yx(2) have "internal_fun(SS)`x = converse(internal_fun(S))`x" by auto
    then show "converse(internal_fun(S)) ` x = internal_fun(SS) ` x" by auto
  }
qed

definition isHyperFinite where
"H\<in>Pow(hyper_set) \<Longrightarrow> isHyperFinite(H) \<equiv> \<exists>S\<in>Pi(I,\<lambda>i. FinPow(X(i))). H = internal_set(S)"

lemma hyperfinite_internal:
  assumes "H\<in>Pow(hyper_set)" "isHyperFinite(H)"
  shows "isInternal(H)"
proof-
  from assms(2) obtain S where S:"S:Pi(I,\<lambda>i. FinPow(X(i)))" "H=internal_set(S)"
    unfolding isHyperFinite_def[OF assms(1)] isInternal_def by auto
  from S(1) have "S:Pi(I,\<lambda>i. Pow(X(i)))" unfolding Pi_def FinPow_def by auto
  with S(2) show ?thesis unfolding isInternal_def by auto
qed

end

end
