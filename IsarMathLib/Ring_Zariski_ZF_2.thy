(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2022  Daniel de la Concepcion

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

section \<open>Rings - Zariski Topology - Properties\<close>

theory Ring_Zariski_ZF_2 imports Ring_Zariski_ZF Topology_ZF_1

begin

theorem (in ring0) zariski_t0:
  shows "{D(I). I\<in>\<I>}{is T\<^sub>0}" unfolding isT0_def
proof-
  {
    fix x y assume ass:"x:Spec" "y:Spec" "x\<noteq>y"
    from ass(3) have "\<not>(x\<subseteq>y) \<or> \<not>(y\<subseteq>x)" by auto
    then have "y\<in>D(x) \<or> x\<in>D(y)" using ass(1,2)
      unfolding Spec_def using ass(1,2) openBasic_def
      by auto
    then have "(x \<in> D(y) \<and> y \<notin> D(y)) \<or> (y \<in> D(x) \<and> x \<notin> D(x))"
      using ass(1,2) unfolding Spec_def
      using openBasic_def by auto
    then have "\<exists>U\<in>{D(I). I\<in>\<I>}. (x \<in> U \<and> y \<notin> U) \<or> (y \<in> U \<and> x \<notin> U)"
      using ass(1,2) unfolding Spec_def by auto
  }
  then show "\<forall>x y. x \<in> \<Union>RepFun(\<I>, D) \<and> y \<in> \<Union>RepFun(\<I>, D) \<and> x \<noteq> y \<longrightarrow>
          (\<exists>U\<in>RepFun(\<I>, D). x \<in> U \<and> y \<notin> U \<or> y \<in> U \<and> x \<notin> U)" 
    using total_spec by auto
qed

text\<open>Noetherian rings have compact Zariski topology\<close>

theorem (in ring0) zariski_compact:
  assumes "\<forall>I\<in>\<I>. (I{is finitely generated})"
  shows "Spec {is compact in} {D(I). I\<in>\<I>}"
  unfolding IsCompact_def
proof(safe)
  show "\<And>x. x \<in> Spec \<Longrightarrow> x \<in> \<Union>RepFun(\<I>, D)" using total_spec by auto
  fix M assume M:"M \<subseteq> RepFun(\<I>, D)" "Spec \<subseteq> \<Union>M"
  let ?J ="{J\<in>\<I>. D(J)\<in>M}"
  have m:"M = RepFun(?J,D)" using M(1) by auto
  then have mm:"\<Union>M = D(\<oplus>\<^sub>I?J)" using union_open_basic[of ?J] by auto
  obtain T where T:"T\<in>FinPow(?J)" "(\<oplus>\<^sub>I?J) = \<oplus>\<^sub>IT" using
    sum_ideals_noetherian[OF assms(1), of ?J] by blast
  from T(2) have "D(\<oplus>\<^sub>I?J) = D(\<oplus>\<^sub>IT)" by auto
  moreover have "T\<subseteq>\<I>" using T(1) unfolding FinPow_def by auto
  ultimately have "D(\<oplus>\<^sub>I?J) = \<Union>RepFun(T,D)" using union_open_basic[of T]
    by auto
  with mm have "\<Union>M = \<Union>RepFun(T,D)" by auto
  then have "Spec \<subseteq> \<Union>RepFun(T,D)" using M(2) by auto moreover
  from T(1) have "RepFun(T,D) \<subseteq> RepFun(?J,D)" unfolding FinPow_def by auto
  with m have "RepFun(T,D) \<subseteq> M" by auto moreover
  from T(1) have "Finite(RepFun(T,D))" unfolding FinPow_def
    using Finite_RepFun by auto
  ultimately show "\<exists>N\<in>FinPow(M). Spec \<subseteq> \<Union>N" unfolding FinPow_def
    by auto
qed
  
end