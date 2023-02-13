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
  assumes "f\<in>surj(T,S)"
  shows "g\<in>target_ring.Spec \<rightarrow> origin_ring.Spec"
proof-
  have "g\<in>target_ring.Spec \<rightarrow> {f-``u. u\<in>target_ring.Spec}" using lam_funtype
    unfolding g_def by auto moreover
  {
    fix t assume "t\<in>{f-``u. u\<in>target_ring.Spec}"
    then obtain u where u:"u:target_ring.Spec" "t=f-``u" by auto
    from u(1) have "u\<triangleleft>\<^sub>pR\<^sub>t" unfolding target_ring.Spec_def by auto
    then have "(f-``u)\<triangleleft>\<^sub>pR\<^sub>o" using preimage_prime_ideal_surj
      assms(2) by auto moreover
    then have "f-``u \<in> origin_ring.ideals"
      unfolding origin_ring.primeIdeal_def
      using origin_ring.ideal_dest_subset by auto
    ultimately have "f-``u \<in> origin_ring.Spec" unfolding origin_ring.Spec_def
      by auto
    with u(2) have "t\<in> origin_ring.Spec" by auto
  }
  then have "{f-``u. u\<in>target_ring.Spec} \<subseteq> origin_ring.Spec" by auto
  ultimately show ?thesis using func1_1_L1B by auto
qed

definition (in ring_homo) spec_cont where
 "spec_cont(h) \<equiv> IsContinuous
           ({target_ring.openBasic(J) . J \<in> target_ring.ideals},
            {origin_ring.openBasic(J) . J \<in> origin_ring.ideals}, h)"

lemma (in ring_homo) spectrum_surj_cont:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(T,S)"
  shows "IsContinuous({target_ring.openBasic(J) . J \<in> target_ring.ideals},{origin_ring.openBasic(J) . J \<in> origin_ring.ideals},g)"
  unfolding IsContinuous_def
proof(safe)
  fix x assume ass:"x\<triangleleft>R\<^sub>o" "x \<subseteq> T"
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
  with G have "target_ring.openBasic(f``x) = g-`` origin_ring.openBasic(x)" by auto
  then show "g -`` origin_ring.openBasic(x) \<in>
           RepFun(target_ring.ideals, target_ring.openBasic)"
    using H by auto
qed

end
