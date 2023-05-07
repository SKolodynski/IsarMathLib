(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2023  Daniel de la Concepcion

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
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Rings - Zariski Topology - maps\<close>

theory Ring_Zariski_ZF_3 imports Ring_Zariski_ZF Ring_ZF_3 Topology_ZF_2

begin

lemma (in ring_homo) spectrum_surj:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "g: target_ring.Spec \<rightarrow> V(ker)"
proof-
  have "g: target_ring.Spec \<rightarrow> {f-``u. u\<in>target_ring.Spec}" using lam_funtype
    unfolding g_def by auto moreover
  {
    fix t assume "t\<in>{f-``u. u\<in>target_ring.Spec}"
    then obtain u where u:"u:target_ring.Spec" "t=f-``u" by auto
    from u(1) have u2:"u\<triangleleft>\<^sub>pR\<^sub>t" unfolding target_ring.Spec_def by auto
    then have "(f-``u)\<triangleleft>\<^sub>pR\<^sub>o" using preimage_prime_ideal_surj
      assms(2) by auto moreover
    then have "f-``u \<in> origin_ring.ideals"
      unfolding origin_ring.primeIdeal_def
      using origin_ring.ideal_dest_subset by auto
    ultimately have "f-``u \<in> origin_ring.Spec" unfolding origin_ring.Spec_def
      by auto
    moreover from u2 have "\<zero>\<^sub>S \<in> u" unfolding
      target_ring.primeIdeal_def using target_ring.ideal_dest_zero
      by auto
    then have "{\<zero>\<^sub>S} \<subseteq> u" by auto
    then have "f-``{\<zero>\<^sub>S} \<subseteq> f-``u" by auto
    moreover have "f-``u \<subseteq> R" using func1_1_L15[OF
      surj_is_fun[OF assms(2)]] by auto
    ultimately have "f-``u \<in> origin_ring.closeBasic(f-``{\<zero>\<^sub>S})"
      using origin_ring.closeBasic_def[of "f-``{\<zero>\<^sub>S}"]
      by force
    with u(2) have "t\<in>origin_ring.closeBasic(f-``{\<zero>\<^sub>S})" by auto
  }
  then have "{f-``u. u\<in>target_ring.Spec} \<subseteq> origin_ring.closeBasic(f-``{\<zero>\<^sub>S})" by auto
  ultimately show ?thesis using func1_1_L1B by auto
qed

lemma (in ring_homo) spectrum_surj_bij:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "g\<in>bij(target_ring.Spec, V(ker))"
proof-
  {
    fix s t assume st:"s\<in>target_ring.Spec" "t\<in>target_ring.Spec"
      "g`s = g`t"
    then have "f-``s = f-``t" using beta unfolding g_def by auto
    then have "f``(f-``s) = f``(f-``t)" by auto
    moreover from st(1,2) have "s \<subseteq> S" "t \<subseteq>S"
      unfolding target_ring.Spec_def origin_ring.Spec_def
      by auto
    moreover note assms(2) st(1,2)
    ultimately have "s=t" using surj_image_vimage
      unfolding target_ring.Spec_def origin_ring.Spec_def 
      by auto
  }
  then have "g\<in>inj(target_ring.Spec, origin_ring.closeBasic(f-``{\<zero>\<^sub>S}))"
    unfolding inj_def using spectrum_surj assms(2) unfolding g_def by auto
  moreover
  {
    fix t assume t:"t\<in>origin_ring.closeBasic(f-``{\<zero>\<^sub>S})"
    then have tt:"t\<in>origin_ring.Spec" "f-``{\<zero>\<^sub>S} \<subseteq> t"
      using origin_ring.closeBasic_def func1_1_L6A[OF surj_is_fun]
      assms(2) by auto
    {
      fix y assume y:"y\<in>f-``(f``t)"
      then have y:"y\<in>R" "f`y\<in>f``t" using func1_1_L15
        surj_is_fun[OF assms(2)] by auto
      from y(2) obtain x where x:"x\<in>t" "f`y = f`x"
        using func_imagedef[OF surj_is_fun]
        assms(2) tt(1) unfolding origin_ring.Spec_def by auto
      from x(2) have "(f`y)\<rs>\<^sub>S(f`x) = (f`x)\<rs>\<^sub>S(f`x)" by auto
      then have "(f`y)\<rs>\<^sub>S(f`x) = \<zero>\<^sub>S" using target_ring.Ring_ZF_1_L3(7)
        apply_type[OF surj_is_fun] assms(2) x(1) tt(1)
        unfolding origin_ring.Spec_def by auto
      then have "f`(y\<rs>\<^sub>Rx) = \<zero>\<^sub>S" using homomor_dest_subs
        x(1) tt(1) y(1) unfolding origin_ring.Spec_def by auto moreover
      from x(1) tt(1) have "x\<in>R" unfolding origin_ring.Spec_def by auto
      with y(1) have "y\<rs>\<^sub>Rx \<in>R" using origin_ring.Ring_ZF_1_L4(2) by auto
      ultimately have "y\<rs>\<^sub>Rx \<in> f-``{\<zero>\<^sub>S}" using func1_1_L15
        surj_is_fun[OF assms(2)] by auto
      then have "y\<rs>\<^sub>Rx \<in>t" using tt(2) by auto moreover
      have "t\<triangleleft>R\<^sub>o" using tt(1) unfolding origin_ring.Spec_def by auto
      ultimately have "x\<ra>\<^sub>R(y\<rs>\<^sub>Rx) \<in>t" using x(1)
        origin_ring.ideal_dest_sum by auto
      then have "y\<in>t" using origin_ring.Ring_ZF_2_L1A(5)
        y(1) \<open>x\<in>R\<close> by auto
    }
    then have "f-``(f``t) = t" using func1_1_L9[of f R S t]
      surj_is_fun[OF assms(2)] tt(1) unfolding origin_ring.Spec_def
      by auto moreover
    then have "(f``t)\<triangleleft>\<^sub>pR\<^sub>t" using prime_ideal_quot_3[of "f``t"]
      assms(2) tt(1) unfolding origin_ring.Spec_def
      using image_ideal_surj[of t] origin_ring.primeIdeal_def[of t]
      by auto
    then have "(f``t)\<triangleleft>\<^sub>pR\<^sub>t" "(f``t)\<triangleleft>R\<^sub>t"
      using target_ring.primeIdeal_def[of "f``t"]
      by auto
    then have "(f``t):target_ring.Spec"
      unfolding target_ring.Spec_def using target_ring.ideal_dest_subset
      by auto moreover
    then have "f-``(f``t) = g`(f``t)" unfolding g_def
      using beta by auto
    ultimately have "g`(f``t) = t" "(f``t):target_ring.Spec" by auto
    then have "\<exists>p\<in>target_ring.Spec. g`p = t" by auto
  }
  ultimately show "g:bij(target_ring.Spec, V(ker))"
    unfolding bij_def surj_def inj_def by auto
qed

definition (in ring_homo) top_origin ("\<tau>\<^sub>o") where
  "top_origin \<equiv> {origin_ring.openBasic(J) . J \<in> origin_ring.ideals}"
  
definition (in ring_homo) top_target ("\<tau>\<^sub>t") where
  "top_target \<equiv> {target_ring.openBasic(J) . J \<in> target_ring.ideals}"

definition (in ring_homo) spec_cont where
 "spec_cont(h) \<equiv> IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o, h)"

lemma (in ring_homo) spectrum_surj_cont:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to}(V(ker)), g)"
  unfolding IsContinuous_def top_target_def RestrictedTo_def top_origin_def
proof(safe)
  fix x assume ass:"x\<triangleleft>R\<^sub>o" "x \<subseteq> R"
  have "origin_ring.openBasic(x) = {u\<in>origin_ring.Spec. \<not>(x \<subseteq> u)}"
    unfolding origin_ring.openBasic_def[OF ass(2)] by auto
  have "g-``(origin_ring.openBasic(x)) = {t\<in>target_ring.Spec. g`t \<in> origin_ring.openBasic(x)}" 
    using spectrum_surj assms(2) unfolding g_def
    using func1_1_L15 by auto
  then have G:"g-``(origin_ring.openBasic(x)) = {t\<in>target_ring.Spec. f-``t \<in> origin_ring.openBasic(x)}"
    using beta unfolding g_def by auto
  have "(f``x)\<triangleleft>R\<^sub>t" using image_ideal_surj assms(2) ass(1) by auto
  then have H:"f``x\<in>target_ring.ideals" using
    target_ring.ideal_dest_subset by auto
  then have F:"target_ring.openBasic(f``x) = {t\<in>target_ring.Spec. \<not>(f``x \<subseteq> t)}"
    using target_ring.openBasic_def by auto
  {
    fix s assume "s\<in>{t\<in>target_ring.Spec. f-``t \<in> origin_ring.openBasic(x)}"
    then have s:"s\<in>target_ring.Spec" "f-``s \<in> origin_ring.openBasic(x)"
      by auto
    from this(2) have E:"f-``s \<in>origin_ring.Spec" "\<not>(x \<subseteq> f-``s)"
      using origin_ring.openBasic_def ass(1) origin_ring.ideal_dest_subset
      by auto
    {
      assume "f``x \<subseteq> s"
      then have "f-``(f``x) \<subseteq> f-``s" by auto
      then have "x \<subseteq> f-``s" using func1_1_L9[OF surj_is_fun]
        assms(2) ass(1) origin_ring.ideal_dest_subset by force
      with E(2) have False by auto
    }
    then have "\<not>(f``x \<subseteq> s)" by auto
    with s(1) have "s\<in>{t\<in>target_ring.Spec. \<not>(f``x \<subseteq> t)}"
      by auto
  }
  then have "{t \<in> target_ring.Spec . f -`` t \<in> origin_ring.openBasic(x)} \<subseteq> {t\<in>target_ring.Spec. \<not>(f``x \<subseteq> t)}"
    by auto moreover
  {
    fix s assume "s\<in>{t\<in>target_ring.Spec. \<not>(f``x \<subseteq> t)}"
    then have s:"s\<in>target_ring.Spec" "\<not>(f``x \<subseteq> s)" by auto
    have "origin_ring.openBasic(x) = {t\<in>origin_ring.Spec. \<not>(x \<subseteq> t)}"
      using origin_ring.openBasic_def ass(1) origin_ring.ideal_dest_subset
      by auto
    {
      assume "x \<subseteq> f-``s"
      then have "f``x \<subseteq> f``(f-``s)" by auto
      then have "f``x \<subseteq> s" using surj_image_vimage
        assms(2) s(1) unfolding target_ring.Spec_def
          target_ring.primeIdeal_def target_ring.ideal_dest_subset
        by auto
      with s(2) have False by auto
    }
    then have "\<not>(x \<subseteq> f-``s)" by auto
    moreover
    from s(1) have "(f-``s) \<triangleleft>\<^sub>pR\<^sub>o" unfolding target_ring.Spec_def
      using preimage_prime_ideal_surj assms(2) by auto
    then have "(f-``s)\<in>origin_ring.Spec" unfolding origin_ring.Spec_def
      origin_ring.primeIdeal_def using origin_ring.ideal_dest_subset
      by auto
    ultimately have "f-``s\<in>origin_ring.openBasic(x)"
      using origin_ring.openBasic_def ass(1)
      origin_ring.ideal_dest_subset by auto
    then have "s\<in>{t \<in> target_ring.Spec . f -`` t \<in> origin_ring.openBasic(x)}"
      using s(1) by auto
  }
  then have "{t \<in> target_ring.Spec . \<not> f `` x \<subseteq> t} \<subseteq> {t \<in> target_ring.Spec . f -`` t \<in> origin_ring.openBasic(x)}"
    by auto
  ultimately have "{t \<in> target_ring.Spec . \<not> f `` x \<subseteq> t} = {t \<in> target_ring.Spec . f -`` t \<in> origin_ring.openBasic(x)}"
    by auto
  with F have "target_ring.openBasic(f``x) = {t \<in> target_ring.Spec . f -`` t \<in> origin_ring.openBasic(x)}"
    by auto
  with G have T:"target_ring.openBasic(f``x) = g-`` origin_ring.openBasic(x)" by auto
  have "g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})) = {t\<in>target_ring.Spec. g`t \<in> origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})}" 
    using spectrum_surj assms(2) unfolding g_def
    using func1_1_L15 by auto
  then have "g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})) = {t\<in>target_ring.Spec. f-``t \<in> origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})}" 
    using beta unfolding g_def by auto
  then have E:"g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})) = {t\<in>target_ring.Spec. f-``t \<in> {q\<in>origin_ring.Spec. (f -`` {\<zero>\<^sub>S}) \<subseteq> q}}" 
    unfolding origin_ring.closeBasic_def[OF func1_1_L3[OF surj_is_fun[OF assms(2)]]] by auto
  {
    fix s assume s:"s\<in>target_ring.openBasic(f``x)"
    with E have ss:"s\<in>target_ring.Spec" "\<not>(f``x \<subseteq> s)" 
      using target_ring.openBasic_def func1_1_L6(2) surj_is_fun[OF assms(2)] by auto
    from this(1) have "g`s \<in> origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})" using spectrum_surj[OF assms(2)]
      apply_type[of g target_ring.Spec "\<lambda>u. origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})"] unfolding g_def
      by auto
    with ss(1) have "f-``s \<in> origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})" using beta
      unfolding g_def by auto
    moreover 
    from ss(1) have "s\<triangleleft>R\<^sub>t" unfolding target_ring.Spec_def
      target_ring.primeIdeal_def by auto
    then have "\<zero>\<^sub>S \<in>s" using target_ring.ideal_dest_zero by auto
    then have "{\<zero>\<^sub>S} \<subseteq> s" by auto
    then have "f-``{\<zero>\<^sub>S} \<subseteq> f-``s" by auto
    moreover
    have "f-``{\<zero>\<^sub>S} \<subseteq> R" using func1_1_L15[OF
      surj_is_fun[OF assms(2)], of "{\<zero>\<^sub>S}"] by auto
    ultimately have "f-``s \<in> {q\<in>origin_ring.Spec. (f -`` {\<zero>\<^sub>S}) \<subseteq> q}"
      using origin_ring.closeBasic_def by auto
    then have "s\<in>{t\<in>target_ring.Spec. f-``t \<in> {q\<in>origin_ring.Spec. (f -`` {\<zero>\<^sub>S}) \<subseteq> q}}"
      using ss(1) by auto
    then have "s\<in>g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S}))" using E by auto
  }
  then have "target_ring.openBasic(f``x) \<subseteq> g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S}))" by auto
  then have "g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S}))\<inter>target_ring.openBasic(f``x) = target_ring.openBasic(f``x)"
    by auto
  with T have "g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})) \<inter> g -`` origin_ring.openBasic(x) = target_ring.openBasic(f``x)"
    by auto moreover
  have "g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S})) \<inter> g -`` origin_ring.openBasic(x) =
    g-``(origin_ring.closeBasic(f -`` {\<zero>\<^sub>S}) \<inter> origin_ring.openBasic(x))"
    using invim_inter_inter_invim[OF spectrum_surj[OF assms(2)]]
    unfolding g_def by auto
  ultimately have "g -``
       (origin_ring.closeBasic(f -`` {\<zero>\<^sub>S}) \<inter>
        origin_ring.openBasic(x)) = target_ring.openBasic(f``x)"
    by auto
  with H show "g -``
       (origin_ring.closeBasic(f -`` {\<zero>\<^sub>S}) \<inter>
        origin_ring.openBasic(x)) \<in>
           RepFun(target_ring.ideals, target_ring.openBasic)"
    by auto
qed

lemma (in ring_homo) spectrum_surj_open:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "\<forall>U\<in>\<tau>\<^sub>t. g``U \<in> \<tau>\<^sub>o {restricted to} V(ker)"
proof
  fix U assume U:"U\<in>\<tau>\<^sub>t"
  then obtain I where I:"I\<triangleleft>R\<^sub>t" "I\<subseteq>S" 
    "U=target_ring.openBasic(I)" unfolding top_target_def
    by auto
  from I(3) have sub:"U \<subseteq> target_ring.Spec" 
    using target_ring.openBasic_def[OF I(2)] by auto
  {
    fix t assume t:"t\<in>g``U"
    then obtain u where u:"u\<in>U" "t=g`u"
      using func_imagedef spectrum_surj[OF assms(2)] sub
      unfolding g_def by auto
    then have t:"t=f-``u" using beta sub unfolding g_def by auto
    with sub u(1) have "t\<triangleleft>\<^sub>pR\<^sub>o" unfolding target_ring.Spec_def
      using preimage_prime_ideal_surj[OF _ assms(2), of u]
      by auto
    then have p:"t\<in>origin_ring.Spec" unfolding origin_ring.Spec_def
      unfolding origin_ring.primeIdeal_def
      using origin_ring.ideal_dest_subset by auto
    from u(1) I(2,3) have Iu:"\<not> (I \<subseteq> u)" using target_ring.openBasic_def
      by auto
    {
      assume "f-``I \<subseteq> t"
      then have "f``(f-``I) \<subseteq> f``t" by auto
      then have "I \<subseteq> f``t" using surj_image_vimage[OF assms(2)] I(2) by auto
      with t have "I \<subseteq> f``(f-``u)" by auto
      moreover from u(1) sub have "u \<subseteq> S"
        unfolding target_ring.Spec_def by auto
      ultimately have "I \<subseteq> u" using surj_image_vimage[OF assms(2)]
        by auto
      with Iu have False by auto
    }
    then have "\<not>(f-``I \<subseteq> t)" by auto
    with p have "t\<in>origin_ring.openBasic(f-``I)"
      using origin_ring.openBasic_def func1_1_L6A[OF surj_is_fun]
      assms(2) by auto
  }
  then have "g``U \<subseteq> origin_ring.openBasic(f-``I)" by auto moreover
  {
    fix t assume t:"t\<in>origin_ring.openBasic(f-``I)" "t\<in>V(ker)"
    have "f-``I \<subseteq> R" using func1_1_L6A[OF surj_is_fun]
      assms(2) by auto
    with t have p:"t\<in>origin_ring.Spec" "\<not>(f-``I \<subseteq> t)"
      using origin_ring.openBasic_def by auto
    from t(2) have kt:"ker \<subseteq> t" using origin_ring.closeBasic_def[OF
      func1_1_L3[OF fun]] by auto
    {
      fix x assume "x\<in>f-``(f``t)"
      then have t:"f`x\<in>f``t" "x\<in>R" using func1_1_L15
        surj_is_fun[OF assms(2)] by auto
      then obtain s where s:"f`x = f`s" "s\<in>t" using
        func_imagedef[OF surj_is_fun[OF assms(2)]]
        p(1) unfolding origin_ring.Spec_def by auto
      from s(2) have ss:"s\<in>R" using p(1) 
        unfolding origin_ring.Spec_def by auto
      from s(1) have "(f`x) \<rs>\<^sub>S (f`s) = \<zero>\<^sub>S" using
        target_ring.Ring_ZF_1_L3(7)[OF apply_type[OF 
            surj_is_fun[OF assms(2)]
        t(2)]] by auto
      then have "f`(x\<rs>\<^sub>Rs) = \<zero>\<^sub>S" using homomor_dest_subs
        t(2) ss by auto moreover
      from t(2) ss have "x\<rs>\<^sub>Rs \<in>R" using origin_ring.Ring_ZF_1_L4(2) by auto
      ultimately have "x\<rs>\<^sub>Rs \<in> f-``{\<zero>\<^sub>S}" using func1_1_L15
        surj_is_fun[OF assms(2)] by auto
      then have "x\<rs>\<^sub>Rs \<in> t" using kt by auto
      then have "s\<ra>\<^sub>R(x\<rs>\<^sub>Rs) \<in> t" 
        using origin_ring.ideal_dest_sum
        s(2) p(1) unfolding origin_ring.Spec_def by auto
      then have "x\<in>t" using origin_ring.Ring_ZF_2_L1A(5)
        ss t(2) by auto
    }
    then have eq:"f-``(f``t) = t"
      using func1_1_L9[OF surj_is_fun[OF assms(2)]
      origin_ring.ideal_dest_subset[of t]] p(1) unfolding origin_ring.Spec_def
      origin_ring.primeIdeal_def by auto
    then have "(f `` t)\<triangleleft>R\<^sub>t \<Longrightarrow> (f``t)\<triangleleft>\<^sub>pR\<^sub>t"
      using prime_ideal_quot_3[of "f``t"] assms(2)
      p(1) unfolding origin_ring.Spec_def by auto
    then have id:"(f``t)\<triangleleft>\<^sub>pR\<^sub>t" "(f `` t)\<triangleleft>R\<^sub>t" using image_ideal_surj
      p(1) assms(2) unfolding origin_ring.Spec_def by auto
    {
      assume "I \<subseteq> f``t"
      then have "f-``I \<subseteq> f-``(f``t)" by auto
      with eq have "f-``I \<subseteq> t" by auto
      with p(2) have False by auto
    }
    then have "\<not>(I \<subseteq> f``t)" by auto
    then have "f``t\<in>target_ring.openBasic(I)"
      using id target_ring.ideal_dest_subset unfolding target_ring.openBasic_def[OF I(2)]
      target_ring.Spec_def by auto
    then have q:"f``t \<in>U" using I(3) by auto
    then have q2:"f``t\<in>target_ring.Spec" using sub by auto
    from q have "g`(f``t) \<in>g``U" using func1_1_L15D[OF bij_is_fun
      [OF spectrum_surj_bij[OF assms(2)]], of "f``t" U]
      unfolding g_def using sub by auto
    then have "f-``(f``t) \<in> g``U" using beta[of "f``t"
      target_ring.Spec "\<lambda>o. f-``o"] q2
      unfolding g_def by auto
    with eq have "t\<in>g``U" by auto
  }
  then have "V(ker)\<inter>D(f -`` I) \<subseteq> g``U" by auto
  ultimately
  have "V(ker)\<inter>D(f -`` I) = g``U"
    using func1_1_L6(2)[OF bij_is_fun[OF
    spectrum_surj_bij[OF assms(2)]],of U] 
    unfolding g_def by blast
  moreover
  have "D(f -`` I) \<in>\<tau>\<^sub>o" unfolding top_origin_def
    using preimage_ideal(1)[OF I(1)]
      origin_ring.ideal_dest_subset by auto
  then have "V(ker)\<inter>D(f -`` I) \<in> {V(ker) \<inter> A . A \<in> \<tau>\<^sub>o}"
    by auto
  ultimately show "g``U:  \<tau>\<^sub>o{restricted to}V(ker)"
    unfolding RestrictedTo_def by auto
qed

text\<open>A quotient ring has a spectrum homeomorphic
to a closed subspace of the spectrum of the base ring.
Specifically, the closed subspace associated to the
ideal by which we quotient.\<close>

corollary (in ring_homo) surj_homeomorphism:
  assumes "f\<in>surj(R,S)"
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f -`` u"
  shows "IsAhomeomorphism(\<tau>\<^sub>t, \<tau>\<^sub>o{restricted to}V(ker), g)"
proof-
  have "\<Union>(\<tau>\<^sub>o{restricted to}V(ker)) = origin_ring.Spec \<inter> V(ker)" unfolding
    top_origin_def RestrictedTo_def using origin_ring.total_spec
    by auto
  then have "\<Union>(\<tau>\<^sub>o{restricted to}V(ker)) = V(ker)"
    using origin_ring.closeBasic_def[OF func1_1_L3[OF fun,
    of "{\<zero>\<^sub>S}"]] by auto moreover
  have "\<Union>\<tau>\<^sub>t = target_ring.Spec" unfolding top_target_def
    using target_ring.total_spec by auto
  ultimately show ?thesis using bij_cont_open_homeo[of g \<tau>\<^sub>t "\<tau>\<^sub>o{restricted to}V(ker)"]
    spectrum_surj_bij[OF assms(1)] spectrum_surj_open[OF assms(1)]
    spectrum_surj_cont[OF assms(1)]
    unfolding g_def by auto
qed
  
end
