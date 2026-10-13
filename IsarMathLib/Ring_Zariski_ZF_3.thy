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

section \<open>The spectrum of a localization\<close>

theory Ring_Zariski_ZF_3 imports Ring_Zariski_ZF_1 Ring_ZF_7

begin

text\<open>In this file we apply the results about the maps induced on prime spectra
  to the canonical homomorphism $R\to S^{-1}R$ from a commutative ring to its localization.
  The localization is commutative, so the preimage of a prime ideal is prime. Since the ideals of
  a localization are extended, the induced map is a homeomorphism from the spectrum of
  the localization onto its image in the spectrum of $R$.\<close>

subsection\<open>The induced map for a localization\<close>

text\<open>The preimage of a prime ideal of the localization along the canonical map is a prime ideal
  of the original ring.\<close>

lemma (in mult_subset) localization_preimage_prime:
  shows "\<forall>u\<in>loc_ring.Spec. LocalizationMap(R,M,S)-``u \<in> Spec"
  using loc_homomorphism.spectrum_prime_preimage_comm loc_mul_comm_assoc(1) by simp

text\<open>The induced map on spectra of a localization is continuous with respect to the Zariski
  topologies, where the spectrum of $R$ is restricted to the closed set defined
  by the kernel of the canonical map.\<close>

lemma (in mult_subset) localization_spec_cont:
  shows "IsContinuous(loc_homomorphism.top_target,
    loc_homomorphism.top_origin {restricted to} (closeBasic(LocalizationMap(R,M,S)-``{TheNeutralElement(Localization(R,M,S),
    LocalizedAdd(R,A,M,S))})),
    \<lambda>u\<in>loc_ring.Spec. LocalizationMap(R,M,S)-``u)"
  using loc_homomorphism.spectrum_comm_cont loc_mul_comm_assoc(1) by blast

subsection\<open>Homeomorphism onto the image\<close>

text\<open>The induced map on spectra of a localization is a homeomorphism from the spectrum of the
  localization onto its image in the spectrum of $R$ with the subspace topology.\<close>

theorem (in mult_subset) localization_spec_homeomorphism:
  shows "IsAhomeomorphism(loc_homomorphism.top_target,
    loc_homomorphism.top_origin {restricted to} {LocalizationMap(R,M,S)-``u. u\<in>loc_ring.Spec},
    \<lambda>u\<in>loc_ring.Spec. LocalizationMap(R,M,S)-``u)"
  using loc_homomorphism.spectrum_map_homeomorphism localization_preimage_prime
    localization_ideals_extended by simp

subsection\<open>The image is the set of primes disjoint from $S$\<close>

text\<open>The image of the spectrum of the localization under the induced map is the set of
  prime ideals of $R$ that do not meet $S$.\<close>

theorem (in mult_subset) localization_spec_image:
  shows "{LocalizationMap(R,M,S)-``u. u\<in>loc_ring.Spec} = {p\<in>Spec. p\<inter>S = 0}"
  unfolding Spec_def loc_ring.Spec_def using localization_prime_image by auto

text\<open>Hence the spectrum of the localization is homeomorphic to the subspace of $\mathrm{Spec}(R)$
  consisting of the prime ideals disjoint from $S$.\<close>

theorem (in mult_subset) localization_spec_homeomorphism_disjoint:
  shows "IsAhomeomorphism(loc_homomorphism.top_target,
    loc_homomorphism.top_origin {restricted to} {p\<in>Spec. p\<inter>S = 0},
    \<lambda>u\<in>loc_ring.Spec. LocalizationMap(R,M,S)-``u)"
  using localization_spec_homeomorphism localization_spec_image by simp

subsection\<open>The spectrum of $R_a$ and the basic open set $D(a)$\<close>

text\<open>The prime ideals of $R$ disjoint from the powers of $a$ are exactly the points of the
  basic open set $D(\{a\})$.\<close>

lemma (in ring_element) powers_disjoint_is_open:
  shows "{p\<in>Spec. p\<inter>ElementPowers(R,M,c) = 0} = D({c})"
proof-
  from a_in have sub:"{c} \<subseteq> R" by auto
  have "\<forall>p\<in>Spec. p\<inter>ElementPowers(R,M,c) = 0 \<longleftrightarrow> \<not>({c} \<subseteq> p)"
    using prime_disjoint_powers unfolding Spec_def by auto
  then show ?thesis using sub openBasic_def by auto
qed

text\<open>The spectrum of the localization $R_a$ of a commutative ring at the powers of an element $a$
  is homeomorphic, via the preimage along the canonical map, to the basic open set $D(a)$
  of the spectrum of $R$ with the subspace topology.\<close>

theorem (in ring_element) element_spec_homeomorphism:
  shows "IsAhomeomorphism(element_loc.loc_homomorphism.top_target,
    element_loc.loc_homomorphism.top_origin {restricted to} D({c}),
    \<lambda>u\<in>element_loc.loc_ring.Spec. LocalizationMap(R,M,ElementPowers(R,M,c))-``u)"
  using element_loc.localization_spec_homeomorphism_disjoint powers_disjoint_is_open by simp

end
