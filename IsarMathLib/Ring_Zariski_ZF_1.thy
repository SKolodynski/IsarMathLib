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

section \<open>Ring homomorphisms as continuous maps on Spec\<close>

theory Ring_Zariski_ZF_1 imports Ring_Zariski_ZF Ring_ZF_3 Topology_ZF_2

begin

text\<open>Every ring homomorphism $f: R \to S$ induces a map $f^*: \mathrm{Spec}(S) \to \mathrm{Spec}(R)$
  on prime spectra by pulling back prime ideals. This file shows that $f^*$ is continuous with
  respect to the Zariski topologies on $\mathrm{Spec}(R)$ and $\mathrm{Spec}(S)$, establishing
  $\mathrm{Spec}$ as a contravariant functor from commutative rings to topological spaces.\<close>

subsection\<open>Induced maps on spectra\<close>

text\<open>An element of the spectrum of the target ring is a prime ideal, an ideal, and a subset of $S$.\<close>

lemma (in ring_homo) target_spec_dest:
  assumes "u\<in>target_ring.Spec"
  shows "u\<triangleleft>\<^sub>pR\<^sub>t" "u\<triangleleft>R\<^sub>t" "u\<subseteq>S"
proof-
  from assms show p:"u\<triangleleft>\<^sub>pR\<^sub>t" unfolding target_ring.Spec_def by auto
  from p show i:"u\<triangleleft>R\<^sub>t" using target_ring.primeIdeal_def by auto
  from i show "u\<subseteq>S" using target_ring.ideal_dest_subset by auto
qed

text\<open>If preimages of primes are prime then the preimage of every prime ideal of the target ring
  contains the kernel, hence it belongs to the V-set of the kernel.\<close>

lemma (in ring_homo) spectrum_prime_preimage_kernel:
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
  shows "\<forall>u\<in>target_ring.Spec. f-``u \<in> V\<^sub>S(ker)"
proof
  fix u assume u:"u\<in>target_ring.Spec"
  have sub:"f-``{\<zero>\<^sub>S} \<subseteq> R" using func1_1_L3 f_is_fun by auto
  then have clo:"origin_ring.closeBasic(f-``{\<zero>\<^sub>S}) = {K\<in>origin_ring.Spec. f-``{\<zero>\<^sub>S} \<subseteq> K}"
    using origin_ring.closeBasic_def by auto
  from u have "u\<triangleleft>R\<^sub>t" using target_spec_dest by auto
  then have "\<zero>\<^sub>S \<in> u" using target_ring.ideal_dest_zero by auto
  then have "{\<zero>\<^sub>S} \<subseteq> u" by auto
  then have "f-``{\<zero>\<^sub>S} \<subseteq> f-``u" by auto
  moreover from assms u have "f-``u \<in> origin_ring.Spec" by auto
  ultimately show "f-``u \<in> origin_ring.closeBasic(f-``{\<zero>\<^sub>S})" using clo by auto
qed

text\<open>If the preimage of every prime ideal of the target ring is a prime ideal of the origin ring,
  then pulling back prime ideals defines a map between the prime spectra
  that lands in the closed set defined by the kernel.\<close>

lemma (in ring_homo) spectrum_map:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
  shows "g: target_ring.Spec \<rightarrow> V\<^sub>S(ker)"
proof-
  have "g: target_ring.Spec \<rightarrow> {f-``u. u\<in>target_ring.Spec}" using lam_funtype
    unfolding g_def by auto moreover
  have "{f-``u. u\<in>target_ring.Spec} \<subseteq> V\<^sub>S(ker)"
    using spectrum_prime_preimage_kernel assms(2) by auto
  ultimately show ?thesis using func1_1_L1B by auto
qed

text\<open>The hypothesis of \<open>spectrum_map\<close> holds when the homomorphism is surjective.\<close>

lemma (in ring_homo) spectrum_prime_preimage_surj:
  assumes "f\<in>surj(R,S)"
  shows "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
proof
  fix u assume "u\<in>target_ring.Spec"
  then have "u\<triangleleft>\<^sub>pR\<^sub>t" unfolding target_ring.Spec_def by auto
  with assms have "(f-``u)\<triangleleft>\<^sub>pR\<^sub>o" using preimage_prime_ideal_surj by auto
  then show "f-``u \<in> origin_ring.Spec" unfolding origin_ring.Spec_def
    origin_ring.primeIdeal_def using origin_ring.ideal_dest_subset by auto
qed

text\<open>The hypothesis of \<open>spectrum_map\<close> also holds when the target ring is commutative.\<close>

lemma (in ring_homo) spectrum_prime_preimage_comm:
  assumes "V {is commutative on} S"
  shows "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
proof
  fix u assume "u\<in>target_ring.Spec"
  then have "u\<triangleleft>\<^sub>pR\<^sub>t" unfolding target_ring.Spec_def by auto
  with assms have "(f-``u)\<triangleleft>\<^sub>pR\<^sub>o" using preimage_prime_ideal_comm by auto
  then show "f-``u \<in> origin_ring.Spec" unfolding origin_ring.Spec_def
    origin_ring.primeIdeal_def using origin_ring.ideal_dest_subset by auto
qed

text\<open>A surjective ring homomorphism induces a map between the prime spectra that lands in the closed set defined by the kernel.\<close>

lemma (in ring_homo) spectrum_surj:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "g: target_ring.Spec \<rightarrow> V\<^sub>S(ker)"
  using spectrum_map spectrum_prime_preimage_surj assms(2)
  unfolding g_def by auto

text\<open>The induced map on spectra is a bijection onto the V-set of the kernel.\<close>

lemma (in ring_homo) spectrum_surj_bij:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "g\<in>bij(target_ring.Spec, V\<^sub>S(ker))"
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
      by auto
    from tt(1) have "t\<triangleleft>\<^sub>pR\<^sub>o" unfolding origin_ring.Spec_def by auto
    with tt(2) assms(2) have "(f``t)\<triangleleft>\<^sub>pR\<^sub>t"
      using preimage_ideal_prime by auto
    then have "(f``t)\<triangleleft>\<^sub>pR\<^sub>t" "(f``t)\<triangleleft>R\<^sub>t"
      using target_ring.primeIdeal_def[of "f``t"]
      by auto
    then have "(f``t):target_ring.Spec"
      unfolding target_ring.Spec_def using target_ring.ideal_dest_subset
      by auto
    then have "g`(f``t) = f-``(f``t)" unfolding g_def
      using beta by auto
    with \<open>f-``(f``t) = t\<close> have "g`(f``t) = t" by auto
    with \<open>(f``t):target_ring.Spec\<close> have "\<exists>p\<in>target_ring.Spec. g`p = t" by auto
  }
  ultimately show "g:bij(target_ring.Spec, V\<^sub>S(ker))"
    unfolding bij_def surj_def inj_def by auto
qed

subsection\<open>Continuity of the induced map\<close>

text\<open>We define the Zariski topologies on origin and target spectra, then show the induced map is continuous and open.\<close>

text\<open>The Zariski topology on the origin ring's spectrum.\<close>

definition (in ring_homo) top_origin ("\<tau>\<^sub>o") where
  "top_origin \<equiv> {origin_ring.openBasic(J) . J \<in> origin_ring.ideals}"

text\<open>The Zariski topology on the target ring's spectrum.\<close>

definition (in ring_homo) top_target ("\<tau>\<^sub>t") where
  "top_target \<equiv> {target_ring.openBasic(J) . J \<in> target_ring.ideals}"

text\<open>Continuity of a map between spectra with respect to the Zariski topologies.\<close>

definition (in ring_homo) spec_cont where
 "spec_cont(h) \<equiv> IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o, h)"

text\<open>For subsets $x\subseteq R$ and $t\subseteq S$ the image of $x$ is contained in $t$
  iff $x$ is contained in the preimage of $t$. This holds for any function.\<close>

lemma (in ring_homo) image_subset_iff_subset_vimage:
  assumes "x \<subseteq> R" "t \<subseteq> S"
  shows "f``x \<subseteq> t \<longleftrightarrow> x \<subseteq> f-``t"
proof
  assume as:"f``x \<subseteq> t"
  { fix y assume y:"y\<in>x"
    with assms(1) have "y\<in>R" by auto
    have "f``x = {f`z. z\<in>x}" using func_imagedef f_is_fun assms(1) by auto
    with y have "f`y \<in> f``x" by auto
    with as have "f`y \<in> t" by auto
    with \<open>y\<in>R\<close> have "y \<in> f-``t" using func1_1_L15 f_is_fun by auto
  }
  then show "x \<subseteq> f-``t" by auto
next
  assume as:"x \<subseteq> f-``t"
  { fix s assume "s\<in>f``x"
    moreover have "f``x = {f`z. z\<in>x}" using func_imagedef f_is_fun assms(1) by auto
    ultimately obtain y where y:"y\<in>x" "s=f`y" by auto
    with as have "f`y \<in> t" using func1_1_L15 f_is_fun by auto
    with y(2) have "s\<in>t" by auto
  }
  then show "f``x \<subseteq> t" by auto
qed

text\<open>The preimage under the induced map of the basic open set \<open>D(x)\<close> of the origin spectrum
  is the basic open set \<open>D(f``x)\<close> of the target spectrum. This only requires that the induced
  map is well defined, not that the homomorphism is surjective.\<close>

lemma (in ring_homo) spectrum_map_vimage_open:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec" "x \<subseteq> R"
  shows "g-``(origin_ring.openBasic(x)) = target_ring.openBasic(f``x)"
proof-
  have gfun:"g: target_ring.Spec \<rightarrow> V\<^sub>S(ker)"
    using spectrum_map assms(2) unfolding g_def by auto
  have fx:"f``x \<subseteq> S" using func1_1_L6(2) f_is_fun by auto
  have key:"\<forall>t\<in>target_ring.Spec. g`t \<in> origin_ring.openBasic(x) \<longleftrightarrow>
    t \<in> target_ring.openBasic(f``x)"
  proof
    fix t assume t:"t\<in>target_ring.Spec"
    from t have tS:"t\<subseteq>S" using target_spec_dest by auto
    from t have gt:"g`t = f-``t" unfolding g_def using beta by auto
    from t assms(2) have tp:"f-``t \<in> origin_ring.Spec" by auto
    have a:"f-``t \<in> origin_ring.openBasic(x) \<longleftrightarrow> \<not>(x \<subseteq> f-``t)"
      using tp origin_ring.openBasic_def assms(3) by auto
    have b:"t \<in> target_ring.openBasic(f``x) \<longleftrightarrow> \<not>(f``x \<subseteq> t)"
      using t target_ring.openBasic_def fx by auto
    have c:"f``x \<subseteq> t \<longleftrightarrow> x \<subseteq> f-``t"
      using image_subset_iff_subset_vimage assms(3) tS by auto
    from a b c gt show "g`t \<in> origin_ring.openBasic(x) \<longleftrightarrow>
      t \<in> target_ring.openBasic(f``x)" by auto
  qed
  show ?thesis
  proof
    { fix t assume "t \<in> g-``(origin_ring.openBasic(x))"
      then have "t\<in>target_ring.Spec" "g`t \<in> origin_ring.openBasic(x)"
        using func1_1_L15 gfun by auto
      with key have "t \<in> target_ring.openBasic(f``x)" by auto
    }
    then show "g-``(origin_ring.openBasic(x)) \<subseteq> target_ring.openBasic(f``x)" by auto
    { fix t assume t:"t \<in> target_ring.openBasic(f``x)"
      then have ts:"t\<in>target_ring.Spec" using target_ring.openBasic_def fx by auto
      with key t have "g`t \<in> origin_ring.openBasic(x)" by auto
      with ts have "t \<in> g-``(origin_ring.openBasic(x))" using func1_1_L15 gfun by auto
    }
    then show "target_ring.openBasic(f``x) \<subseteq> g-``(origin_ring.openBasic(x))" by auto
  qed
qed

text\<open>The preimage of a closed basic set \<open>V(x)\<close> of the origin spectrum is the closed basic set
  \<open>V(f``x)\<close> of the target spectrum.\<close>

lemma (in ring_homo) spectrum_map_vimage_closed:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec" "x \<subseteq> R"
  shows "g-``(origin_ring.closeBasic(x)) = target_ring.closeBasic(f``x)"
proof-
  have gfun:"g: target_ring.Spec \<rightarrow> V\<^sub>S(ker)"
    using spectrum_map assms(2) unfolding g_def by auto
  have fx:"f``x \<subseteq> S" using func1_1_L6(2) f_is_fun by auto
  have key:"\<forall>t\<in>target_ring.Spec. g`t \<in> origin_ring.closeBasic(x) \<longleftrightarrow>
    t \<in> target_ring.closeBasic(f``x)"
  proof
    fix t assume t:"t\<in>target_ring.Spec"
    from t have tS:"t\<subseteq>S" using target_spec_dest by auto
    from t have gt:"g`t = f-``t" unfolding g_def using beta by auto
    from t assms(2) have tp:"f-``t \<in> origin_ring.Spec" by auto
    have a:"f-``t \<in> origin_ring.closeBasic(x) \<longleftrightarrow> x \<subseteq> f-``t"
      using tp origin_ring.closeBasic_def assms(3) by auto
    have b:"t \<in> target_ring.closeBasic(f``x) \<longleftrightarrow> f``x \<subseteq> t"
      using t target_ring.closeBasic_def fx by auto
    have c:"f``x \<subseteq> t \<longleftrightarrow> x \<subseteq> f-``t"
      using image_subset_iff_subset_vimage assms(3) tS by auto
    from a b c gt show "g`t \<in> origin_ring.closeBasic(x) \<longleftrightarrow>
      t \<in> target_ring.closeBasic(f``x)" by auto
  qed
  show ?thesis
  proof
    { fix t assume "t \<in> g-``(origin_ring.closeBasic(x))"
      then have "t\<in>target_ring.Spec" "g`t \<in> origin_ring.closeBasic(x)"
        using func1_1_L15 gfun by auto
      with key have "t \<in> target_ring.closeBasic(f``x)" by auto
    }
    then show "g-``(origin_ring.closeBasic(x)) \<subseteq> target_ring.closeBasic(f``x)" by auto
    { fix t assume t:"t \<in> target_ring.closeBasic(f``x)"
      then have ts:"t\<in>target_ring.Spec" using target_ring.closeBasic_def fx by auto
      with key t have "g`t \<in> origin_ring.closeBasic(x)" by auto
      with ts have "t \<in> g-``(origin_ring.closeBasic(x))" using func1_1_L15 gfun by auto
    }
    then show "target_ring.closeBasic(f``x) \<subseteq> g-``(origin_ring.closeBasic(x))" by auto
  qed
qed

text\<open>The induced map on spectra is continuous with respect to the Zariski topologies,
  where the topology of the origin spectrum is restricted to any set \<open>W\<close> containing
  the image of the map. This holds whenever the preimages of prime ideals are prime ideals,
  in particular the homomorphism does not have to be surjective.\<close>

lemma (in ring_homo) spectrum_map_cont:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
    "\<forall>u\<in>target_ring.Spec. f-``u \<in> W"
  shows "IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to} W, g)"
  unfolding IsContinuous_def top_target_def RestrictedTo_def top_origin_def
proof(safe)
  fix x assume ass:"x\<triangleleft>R\<^sub>o" "x \<subseteq> R"
  have gfun:"g: target_ring.Spec \<rightarrow> W"
  proof-
    have "g: target_ring.Spec \<rightarrow> {f-``u. u\<in>target_ring.Spec}" using lam_funtype
      unfolding g_def by auto
    moreover have "{f-``u. u\<in>target_ring.Spec} \<subseteq> W" using assms(3) by auto
    ultimately show ?thesis using func1_1_L1B by auto
  qed
  have vo:"g-``(origin_ring.openBasic(x)) = target_ring.openBasic(f``x)"
    using spectrum_map_vimage_open assms(2) ass(2) unfolding g_def by auto
  have fx:"f``x \<subseteq> S" using func1_1_L6(2) f_is_fun by auto
  have eq:"g-``(W \<inter> origin_ring.openBasic(x)) = target_ring.openBasic(f``x)"
  proof
    { fix t assume "t \<in> g-``(W \<inter> origin_ring.openBasic(x))"
      then have "t \<in> g-``(origin_ring.openBasic(x))" by auto
      with vo have "t \<in> target_ring.openBasic(f``x)" by auto
    }
    then show "g-``(W \<inter> origin_ring.openBasic(x)) \<subseteq> target_ring.openBasic(f``x)" by auto
    { fix t assume "t \<in> target_ring.openBasic(f``x)"
      with vo have t:"t \<in> g-``(origin_ring.openBasic(x))" by auto
      then have ts:"t\<in>target_ring.Spec" "g`t \<in> origin_ring.openBasic(x)"
        using func1_1_L15 gfun by auto
      from ts(1) gfun have "g`t \<in> W" using apply_type by auto
      with ts(2) have "g`t \<in> W \<inter> origin_ring.openBasic(x)" by auto
      with ts(1) have "t \<in> g-``(W \<inter> origin_ring.openBasic(x))"
        using func1_1_L15 gfun by auto
    }
    then show "target_ring.openBasic(f``x) \<subseteq> g-``(W \<inter> origin_ring.openBasic(x))" by auto
  qed
  have "\<exists>J\<in>target_ring.ideals. target_ring.openBasic(f``x) = target_ring.openBasic(J)"
    using target_ring.D_operator_only_ideals[of "f``x"] fx 
      target_ring.generated_ideal_is_ideal[of "f``x"]
      target_ring.ideal_dest_subset[of "target_ring.generatedIdeal(f `` x)"] by auto
  then obtain J where "J\<in>target_ring.ideals" "target_ring.openBasic(f``x) = target_ring.openBasic(J)"
    by auto
  with eq show "g -`` (W \<inter> origin_ring.openBasic(x)) \<in>
           RepFun(target_ring.ideals, target_ring.openBasic)"
    by auto
qed

text\<open>For a surjective homomorphism the induced map on spectra is continuous.\<close>

lemma (in ring_homo) spectrum_surj_cont:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to}(V\<^sub>S(ker)), g)"
proof-
  have h:"\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
    using spectrum_prime_preimage_surj assms(2) by auto
  then have k:"\<forall>u\<in>target_ring.Spec. f-``u \<in> V\<^sub>S(ker)"
    using spectrum_prime_preimage_kernel by auto
  from h k show ?thesis using spectrum_map_cont unfolding g_def by auto
qed

text\<open>The same holds if the target ring is commutative, without assuming surjectivity.\<close>

lemma (in ring_homo) spectrum_comm_cont:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "V {is commutative on} S"
  shows "IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to}(V\<^sub>S(ker)), g)"
proof-
  have h:"\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
    using spectrum_prime_preimage_comm assms(2) by auto
  then have k:"\<forall>u\<in>target_ring.Spec. f-``u \<in> V\<^sub>S(ker)"
    using spectrum_prime_preimage_kernel by auto
  from h k show ?thesis using spectrum_map_cont unfolding g_def by auto
qed

subsection\<open>Openness and homeomorphisms without surjectivity\<close>

text\<open>The induced map on spectra is open and injective, hence a homeomorphism onto its image,
  under a condition on the ideals of the target ring that is implied by surjectivity but
  also holds in other cases.\<close>

text\<open>The ideals of the target ring of a surjective homomorphism are extended.\<close>

lemma (in ring_homo) ideals_extended_surj:
  assumes "f\<in>surj(R,S)"
  shows "ideals_extended"
  unfolding IdealsExtended_def
proof(intro allI impI)
  fix J K assume J:"J\<triangleleft>R\<^sub>t" and Kc:"K\<triangleleft>R\<^sub>t \<and> f``(f-``J) \<subseteq> K"
  from J have "J \<subseteq> S" using target_ring.ideal_dest_subset by auto
  with assms have "f``(f-``J) = J" using surj_image_vimage by auto
  with Kc show "J \<subseteq> K" by auto
qed

text\<open>If the ideals of the target ring are extended, the induced map on spectra is injective
  and hence a bijection onto its image.\<close>

lemma (in ring_homo) spectrum_map_bij:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "ideals_extended"
  shows "g \<in> bij(target_ring.Spec, {f-``u. u\<in>target_ring.Spec})"
proof-
  have gfn:"g: target_ring.Spec \<rightarrow> {f-``u. u\<in>target_ring.Spec}" using lam_funtype
    unfolding g_def by auto
  have sub:"\<forall>u\<in>target_ring.Spec. f-``u \<subseteq> R" using func1_1_L3 f_is_fun by auto
  { fix s t assume st:"s\<in>target_ring.Spec" "t\<in>target_ring.Spec" "g`s = g`t"
    then have eq:"f-``s = f-``t" using beta unfolding g_def by auto
    from st(1,2) have ss:"s\<triangleleft>R\<^sub>t" "s\<subseteq>S" and tt:"t\<triangleleft>R\<^sub>t" "t\<subseteq>S"
      using target_spec_dest by auto
    from st(1,2) sub have rs:"f-``s \<subseteq> R" "f-``t \<subseteq> R" by auto
    have "f``(f-``s) \<subseteq> t \<longleftrightarrow> f-``s \<subseteq> f-``t"
      using image_subset_iff_subset_vimage rs(1) tt(2) by auto
    with eq have "f``(f-``s) \<subseteq> t" by auto
    with assms(2) ss(1) tt(1) have "s \<subseteq> t" using ideals_extended_dest by auto
    moreover
    have "f``(f-``t) \<subseteq> s \<longleftrightarrow> f-``t \<subseteq> f-``s"
      using image_subset_iff_subset_vimage rs(2) ss(2) by auto
    with eq have "f``(f-``t) \<subseteq> s" by auto
    with assms(2) ss(1) tt(1) have "t \<subseteq> s" using ideals_extended_dest by auto
    ultimately have "s = t" by auto
  }
  then have "g \<in> inj(target_ring.Spec, {f-``u. u\<in>target_ring.Spec})"
    unfolding inj_def using gfn by auto
  moreover
  { fix y assume "y \<in> {f-``u. u\<in>target_ring.Spec}"
    then obtain u where u:"u\<in>target_ring.Spec" "y = f-``u" by auto
    then have "g`u = y" unfolding g_def using beta by auto
    with u(1) have "\<exists>x\<in>target_ring.Spec. g`x = y" by auto
  }
  then have "g \<in> surj(target_ring.Spec, {f-``u. u\<in>target_ring.Spec})"
    unfolding surj_def using gfn by auto
  ultimately show ?thesis unfolding bij_def by auto
qed

text\<open>If the ideals of the target ring are extended, the induced map on spectra sends open sets
  to open sets of the topology of the origin spectrum restricted to the image of the map.
  Surjectivity of the homomorphism is not needed.\<close>

lemma (in ring_homo) spectrum_map_open:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec" "ideals_extended"
  shows "\<forall>U\<in>\<tau>\<^sub>t. g``U \<in> \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}"
proof
  fix U assume U:"U\<in>\<tau>\<^sub>t"
  then obtain I where I:"I\<triangleleft>R\<^sub>t" "I\<subseteq>S"
    "U=target_ring.openBasic(I)" unfolding top_target_def
    by auto
  from I(3) have sub:"U \<subseteq> target_ring.Spec"
    using target_ring.openBasic_def I(2) by auto
  have gfun:"g: target_ring.Spec \<rightarrow> V\<^sub>S(ker)"
    using spectrum_map assms(2) unfolding g_def by auto
  have gU:"g``U = {g`u. u\<in>U}" using func_imagedef gfun sub by auto
  have fI:"f-``I \<subseteq> R" using func1_1_L3 f_is_fun by auto
  have eq:"g``U = {f-``u. u\<in>target_ring.Spec} \<inter> origin_ring.openBasic(f-``I)"
  proof
    { fix s assume "s\<in>g``U"
      then obtain u where u:"u\<in>U" "s=g`u" using gU by auto
      with sub have us:"u\<in>target_ring.Spec" by auto
      with u(2) have s:"s=f-``u" unfolding g_def using beta by auto
      from us assms(2) have sp:"f-``u \<in> origin_ring.Spec" by auto
      from us have uI:"u\<triangleleft>R\<^sub>t" "u\<subseteq>S" using target_spec_dest by auto
      from u(1) I(2,3) have Iu:"\<not>(I \<subseteq> u)" using target_ring.openBasic_def
        by auto
      have ii:"f``(f-``I) \<subseteq> u \<longleftrightarrow> f-``I \<subseteq> f-``u"
        using image_subset_iff_subset_vimage fI uI(2) by auto
      { assume "f-``I \<subseteq> f-``u"
        with ii have "f``(f-``I) \<subseteq> u" by auto
        with assms(3) I(1) uI(1) have "I \<subseteq> u" using ideals_extended_dest by auto
        with Iu have False by auto
      }
      then have "\<not>(f-``I \<subseteq> s)" using s by auto
      with sp s have "s \<in> origin_ring.openBasic(f-``I)"
        using origin_ring.openBasic_def fI by auto
      moreover from us s have "s \<in> {f-``u. u\<in>target_ring.Spec}" by auto
      ultimately have "s \<in> {f-``u. u\<in>target_ring.Spec} \<inter> origin_ring.openBasic(f-``I)"
        by auto
    }
    then show "g``U \<subseteq> {f-``u. u\<in>target_ring.Spec} \<inter> origin_ring.openBasic(f-``I)"
      by auto
    { fix s assume s:"s \<in> {f-``u. u\<in>target_ring.Spec} \<inter> origin_ring.openBasic(f-``I)"
      then obtain u where u:"u\<in>target_ring.Spec" "s=f-``u" by auto
      from s have "s \<in> origin_ring.openBasic(f-``I)" by auto
      with fI have nsub:"\<not>(f-``I \<subseteq> s)" using origin_ring.openBasic_def by auto
      { assume "I \<subseteq> u"
        then have "f-``I \<subseteq> f-``u" by auto
        with u(2) nsub have False by auto
      }
      then have "\<not>(I \<subseteq> u)" by auto
      with u(1) have "u \<in> U" using I(3) target_ring.openBasic_def I(2) by auto
      then have "g`u\<in>{g`u. u\<in>U}" by auto
      moreover from u(1) have "g`u = f-``u" unfolding g_def using beta by auto
      ultimately have "f-``u\<in>g``U" using gU by auto
      then have "s \<in> g``U" using u(2) by blast
    }
    then show "{f-``u. u\<in>target_ring.Spec} \<inter> origin_ring.openBasic(f-``I) \<subseteq> g``U"
      by auto
  qed
  from I(1) have "(f-``I) \<triangleleft>R\<^sub>o" using preimage_ideal(2) by auto
  then have "f-``I \<in> origin_ring.ideals" using origin_ring.ideal_dest_subset by auto
  then have "origin_ring.openBasic(f-``I) \<in> \<tau>\<^sub>o" unfolding top_origin_def by auto
  with eq show "g``U \<in> \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}"
    unfolding RestrictedTo_def by auto
qed

text\<open>If the preimages of prime ideals are prime and the ideals of the target ring are extended,
  then the induced map on spectra is a homeomorphism from the spectrum of the target ring onto
  its image in the spectrum of the origin ring. This is the case for surjective homomorphisms
  and for localizations, among others.\<close>

theorem (in ring_homo) spectrum_map_homeomorphism:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec" "ideals_extended"
  shows "IsAhomeomorphism(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}, g)"
proof-
  have bijg:"g \<in> bij(target_ring.Spec, {f-``u. u\<in>target_ring.Spec})"
    using spectrum_map_bij assms(3) unfolding g_def by auto
  have hw:"\<forall>u\<in>target_ring.Spec. f-``u \<in> {f-``u. u\<in>target_ring.Spec}" by auto
  have contg:"IsContinuous(\<tau>\<^sub>t, \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}, g)"
    using spectrum_map_cont assms(2) hw unfolding g_def by auto
  have opng:"\<forall>U\<in>\<tau>\<^sub>t. g``U \<in> \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}"
    using spectrum_map_open assms(2,3) unfolding g_def by auto
  have "\<Union>(\<tau>\<^sub>o{restricted to}{f-``u. u\<in>target_ring.Spec}) =
    origin_ring.Spec \<inter> {f-``u. u\<in>target_ring.Spec}"
    unfolding top_origin_def RestrictedTo_def using origin_ring.total_spec
    by auto
  then have "\<Union>(\<tau>\<^sub>o{restricted to}{f-``u. u\<in>target_ring.Spec}) = {f-``u. u\<in>target_ring.Spec}"
    using assms(2) by auto moreover
  have "\<Union>\<tau>\<^sub>t = target_ring.Spec" unfolding top_target_def
    using target_ring.total_spec by auto
  ultimately show ?thesis
    using bij_cont_open_homeo[of g \<tau>\<^sub>t "\<tau>\<^sub>o{restricted to}{f-``u. u\<in>target_ring.Spec}"]
    bijg contg opng by auto
qed

text\<open>For a surjective homomorphism the image of the induced map on spectra is the
  closed set defined by the kernel.\<close>

lemma (in ring_homo) spectrum_surj_image:
  assumes "f\<in>surj(R,S)"
  shows "{f-``u. u\<in>target_ring.Spec} = V\<^sub>S(ker)"
proof
  have h:"\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
    using spectrum_prime_preimage_surj assms by auto
  then have "\<forall>u\<in>target_ring.Spec. f-``u \<in> V\<^sub>S(ker)"
    using spectrum_prime_preimage_kernel by auto
  then show "{f-``u. u\<in>target_ring.Spec} \<subseteq> V\<^sub>S(ker)" by auto
  have bij:"(\<lambda>u\<in>target_ring.Spec. f-``u) \<in> bij(target_ring.Spec, V\<^sub>S(ker))"
    using spectrum_surj_bij assms by auto
  { fix t assume "t \<in> V\<^sub>S(ker)"
    with bij obtain x where x:"x\<in>target_ring.Spec" "(\<lambda>u\<in>target_ring.Spec. f-``u)`x = t"
      unfolding bij_def surj_def by auto
    then have "t = f-``x" using beta by auto
    with x(1) have "t \<in> {f-``u. u\<in>target_ring.Spec}" by auto
  }
  then show "V\<^sub>S(ker) \<subseteq> {f-``u. u\<in>target_ring.Spec}" by auto
qed

text\<open>The induced map on spectra of a surjective homomorphism sends open sets to open sets
  of the restricted topology.\<close>

lemma (in ring_homo) spectrum_surj_open:
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f-``u"
  assumes "f\<in>surj(R,S)"
  shows "\<forall>U\<in>\<tau>\<^sub>t. g``U \<in> \<tau>\<^sub>o {restricted to} V\<^sub>S(ker)"
proof-
  have h:"\<forall>u\<in>target_ring.Spec. f-``u \<in> origin_ring.Spec"
    using spectrum_prime_preimage_surj assms(2) by auto
  have e:"ideals_extended" using ideals_extended_surj assms(2) by auto
  have "\<forall>U\<in>\<tau>\<^sub>t. g``U \<in> \<tau>\<^sub>o {restricted to} {f-``u. u\<in>target_ring.Spec}"
    using spectrum_map_open h e unfolding g_def by auto
  moreover have W:"V\<^sub>S(ker) = {f-``u. u\<in>target_ring.Spec}"
    using spectrum_surj_image assms(2) by auto
  ultimately show ?thesis unfolding W by simp
qed

text\<open>A quotient ring has a spectrum homeomorphic
to a closed subspace of the spectrum of the base ring.
Specifically, the closed subspace associated to the
ideal by which we quotient.\<close>

corollary (in ring_homo) surj_homeomorphism:
  assumes "f\<in>surj(R,S)"
  defines "g \<equiv> \<lambda>u\<in>target_ring.Spec. f -`` u"
  shows "IsAhomeomorphism(\<tau>\<^sub>t, \<tau>\<^sub>o{restricted to}V\<^sub>S(ker), g)"
proof-
  have "\<Union>(\<tau>\<^sub>o{restricted to}V\<^sub>S(ker)) = origin_ring.Spec \<inter> V\<^sub>S(ker)" unfolding
    top_origin_def RestrictedTo_def using origin_ring.total_spec
    by auto
  then have "\<Union>(\<tau>\<^sub>o{restricted to}V\<^sub>S(ker)) = V\<^sub>S(ker)"
    using origin_ring.closeBasic_def func1_1_L3 f_is_fun
     by auto moreover
  have "\<Union>\<tau>\<^sub>t = target_ring.Spec" unfolding top_target_def
    using target_ring.total_spec by auto
  ultimately show ?thesis using bij_cont_open_homeo[of g \<tau>\<^sub>t "\<tau>\<^sub>o{restricted to}V\<^sub>S(ker)"]
    spectrum_surj_bij[OF assms(1)] spectrum_surj_open[OF assms(1)]
    spectrum_surj_cont[OF assms(1)]
    unfolding g_def by auto
qed

end
