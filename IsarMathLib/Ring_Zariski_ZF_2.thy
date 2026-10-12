(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2026  Daniel de la Concepcion

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

section \<open>Ring homomorphisms to commutative rings and the Zariski topology\<close>

theory Ring_Zariski_ZF_2 imports Ring_Zariski_ZF_1

begin

text\<open>In this file we specialize the results about the maps induced on prime spectra
  to ring homomorphisms whose target ring is commutative. In this case the preimage of a prime ideal
  is always a prime ideal, so the induced map on spectra is defined and continuous
  without any assumption on the homomorphism. We also describe the preimages of the
  basic open and closed sets.\<close>

subsection\<open>The induced map for a commutative target ring\<close>

text\<open>We work in the context of a ring homomorphism whose target ring is commutative.
  The origin ring does not have to be commutative.\<close>

text\<open>The locale \<open>comm_target_homo\<close> is the \<open>ring_homo\<close> locale with the
  additional assumption that the multiplication in the target ring is commutative.\<close>

locale comm_target_homo = ring_homo +
  assumes target_commutative: "V {is commutative on} S"

text\<open>The induced map on spectra sends a prime ideal of the target ring to its preimage.\<close>

definition (in ring_homo) spec_pullback where
  "spec_pullback \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"

text\<open>If the target ring is commutative then the preimage of a prime ideal is a prime ideal.\<close>

lemma (in comm_target_homo) comm_preimage_prime:
  shows "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
  using spectrum_prime_preimage_comm target_commutative by simp

text\<open>The induced map is a function from the spectrum of the target ring
  to the closed set defined by the kernel in the spectrum of the origin ring.\<close>

lemma (in comm_target_homo) spec_pullback_fun:
  shows "spec_pullback: target_ring.Spec \<rightarrow> V\<^sub>S(ker)"
  using spectrum_map comm_preimage_prime unfolding spec_pullback_def by auto

text\<open>The value of the induced map at a prime ideal is its preimage.\<close>

lemma (in comm_target_homo) spec_pullback_val:
  assumes "u\<in>target_ring.Spec"
  shows "spec_pullback`u = f-``u"
  using assms beta unfolding spec_pullback_def by auto

text\<open>The induced map is continuous with respect to the Zariski topologies
  without assuming that the homomorphism is surjective.\<close>

lemma (in comm_target_homo) spec_pullback_cont:
  shows "IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to}(V\<^sub>S(ker)), spec_pullback)"
  using spectrum_comm_cont target_commutative unfolding spec_pullback_def by auto

subsection\<open>Preimages of basic sets\<close>

text\<open>The preimage of the basic open set defined by an element $a$ of the origin ring
  is the basic open set defined by its image $f(a)$.\<close>

lemma (in comm_target_homo) pullback_principal_open:
  assumes "c\<in>R"
  shows "spec_pullback-``(origin_ring.openBasic({c})) = target_ring.openBasic({f`c})"
proof-
  from assms have sub:"{c} \<subseteq> R" by auto
  from assms have img:"f``{c} = {f`c}" using func_imagedef f_is_fun by auto
  have "spec_pullback-``(origin_ring.openBasic({c})) = target_ring.openBasic(f``{c})"
    using spectrum_map_vimage_open comm_preimage_prime sub
    unfolding spec_pullback_def by auto
  with img show ?thesis by simp
qed

text\<open>The preimage of the closed basic set defined by an element $a$ of the origin ring
  is the closed basic set defined by its image $f(a)$.\<close>

lemma (in comm_target_homo) pullback_principal_closed:
  assumes "c\<in>R"
  shows "spec_pullback-``(origin_ring.closeBasic({c})) = target_ring.closeBasic({f`c})"
proof-
  from assms have sub:"{c} \<subseteq> R" by auto
  from assms have img:"f``{c} = {f`c}" using func_imagedef f_is_fun by auto
  have "spec_pullback-``(origin_ring.closeBasic({c})) = target_ring.closeBasic(f``{c})"
    using spectrum_map_vimage_closed comm_preimage_prime sub
    unfolding spec_pullback_def by auto
  with img show ?thesis by simp
qed

text\<open>The preimage of the basic open set defined by a subset $x$ of the origin ring
  is the basic open set defined by the image of $x$.\<close>

lemma (in comm_target_homo) pullback_open:
  assumes "x \<subseteq> R"
  shows "spec_pullback-``(origin_ring.openBasic(x)) = target_ring.openBasic(f``x)"
  using spectrum_map_vimage_open comm_preimage_prime assms
  unfolding spec_pullback_def by auto

text\<open>The preimage of the closed basic set defined by a subset $x$ of the origin ring
  is the closed basic set defined by the image of $x$.\<close>

lemma (in comm_target_homo) pullback_closed:
  assumes "x \<subseteq> R"
  shows "spec_pullback-``(origin_ring.closeBasic(x)) = target_ring.closeBasic(f``x)"
  using spectrum_map_vimage_closed comm_preimage_prime assms
  unfolding spec_pullback_def by auto

subsection\<open>Homeomorphisms onto the image\<close>

text\<open>If the ideals of the target ring are extended (see \<open>ideals_extended\<close> in
  \<open>Ring_Zariski_ZF_1\<close>; this holds for surjective homomorphisms) the induced map is
  a homeomorphism onto its image.\<close>

theorem (in comm_target_homo) spec_pullback_homeomorphism:
  assumes "ideals_extended"
  shows "IsAhomeomorphism(\<tau>\<^sub>t,
    \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}, spec_pullback)"
  using spectrum_map_homeomorphism comm_preimage_prime assms
  unfolding spec_pullback_def by auto

end
