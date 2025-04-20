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

section \<open>Ultrafilters\<close>

theory Ultrafilter_ZF imports Topology_ZF_4 Topology_ZF_examples
begin

text\<open>This theory deals with ultrafilters; which is a maximal filter.\<close>

definition IsUltrafilter ("_{is an ultrafilter on}_" 80)
  where "\<FF>{is an ultrafilter on}X \<equiv> (\<FF>{is a filter on}X) \<and> (\<forall>\<GG>. (\<GG>{is a filter on}X) \<longrightarrow> (\<FF> \<subseteq> \<GG> \<longrightarrow> \<GG> = \<FF>))"

text\<open>Every set or its opposite is in an ultrafilter\<close>

lemma set_ultrafilter:
  assumes "A\<in>Pow(X)" "\<FF>{is an ultrafilter on}X"
  shows "A\<in>\<FF> \<or> (X-A)\<in>\<FF>"
proof-
  from assms(2) have filter:"\<FF>{is a filter on}X" unfolding IsUltrafilter_def by auto
  {
    assume a0:"A\<noteq>0"
    {
      assume a:"A\<notin>\<FF>" "X-A\<notin>\<FF>"
      then obtain \<GG> where g:"\<GG>{is a filter on}X" "A \<in> \<GG>" "\<FF> \<subseteq> \<GG>"
        using extend_filter[OF assms(1) _ a0, of \<FF>] filter by auto
      with assms(2) have "A\<in>\<FF>" unfolding IsUltrafilter_def by auto
      with a have False by auto
    }
    then have "A\<in>\<FF> \<or> (X-A)\<in>\<FF>" by auto
  } moreover
  {
    assume "A=0"
    then have "X-A=X" by auto
    then have "X-A\<in>\<FF>" using filter unfolding IsFilter_def by auto
    then have "A\<in>\<FF> \<or> (X-A)\<in>\<FF>" by auto
  } ultimately
  show "A\<in>\<FF> \<or> (X-A)\<in>\<FF>" by blast
qed

text\<open>It contains only one of them\<close>

lemma only_set_or_opposite:
  assumes "A\<in>Pow(X)" "\<FF>{is a filter on}X" "A\<in>\<FF>"
  shows "(X-A)\<notin>\<FF>"
proof
  assume "X-A\<in>\<FF>"
  with assms have "A\<inter>(X-A)\<in>\<FF>" using is_filter_def_split(4) by auto
  moreover have "A\<inter>(X-A) = 0" by auto
  ultimately have "0\<in>\<FF>" by auto
  then show False using assms(2) is_filter_def_split(1) by auto
qed

text\<open>If a filter contains a set or its opposite, it is in an ultrafilter\<close>

lemma set_ultrafilter_equiv:
  assumes "\<FF>{is a filter on}X" "\<forall>A\<in>Pow(X). A\<in>\<FF> \<or> (X-A)\<in>\<FF>"
  shows "\<FF>{is an ultrafilter on}X" unfolding IsUltrafilter_def
proof(safe)
  from assms(1) show "\<FF>{is a filter on}X".
  {
    fix \<GG> assume g:"\<GG>{is a filter on}X" "\<FF> \<subseteq> \<GG>"
    {
      assume "\<GG>\<noteq>\<FF>"
      with g(2) obtain h where h:"h:\<GG>" "h\<notin>\<FF>" by auto
      from h(1) g(1) have "h\<in>Pow(X)" "h\<noteq>0" unfolding IsFilter_def by auto
      with assms(2) h(2) have "X-h\<in>\<FF>" by auto
      with g(2) have "X-h:\<GG>" by auto
      with h(1) g(1) have "(X-h)\<inter>h\<in>\<GG>" unfolding IsFilter_def by auto moreover
      have "(X-h)\<inter>h=0" by auto ultimately
      have "0\<in>\<GG>" by auto
      with g(1) have False unfolding IsFilter_def by auto
    }
    then show "\<GG>=\<FF>" by auto
  }
qed

text\<open>Filters of containing a point, are ultrafilters\<close>

lemma include_point_ultrafilter:
  assumes "x\<in>X"
  shows "{A\<in>Pow(X). x\<in>A}{is an ultrafilter on}X"
proof(rule set_ultrafilter_equiv)
  show "{A \<in> Pow(X) . x \<in> A} {is a filter on} X" unfolding IsFilter_def
    apply safe using assms apply simp by auto
  {
    fix A assume A:"A\<in>Pow(X)"
    have "x:A \<or> x\<notin>A" by auto
    with assms have "x\<in>A \<or> x\<in>X-A" by auto
    with A(1) have "A\<in>{A \<in> Pow(X) . x \<in> A} \<or> X-A: {A \<in> Pow(X) . x \<in> A} " by auto
  }
  then show "\<forall>A\<in>Pow(X). A \<in> {A \<in> Pow(X) . x \<in> A} \<or> X - A \<in> {A \<in> Pow(X) . x \<in> A}" by auto
qed

text\<open>An ultrafilter that has no singleton sets, does not have finite sets\<close>

lemma ultrafilter_finite_set:
  assumes "\<FF>{is an ultrafilter on}X" "\<forall>x\<in>X. {x}\<notin>\<FF>" "A\<in>FinPow(X)"
  shows "A\<notin>\<FF>"
proof(rule FinPow_induct[of "\<lambda>q. q\<notin>\<FF>"])
  from assms(1) show "0\<notin>\<FF>" unfolding IsUltrafilter_def IsFilter_def by auto
  show "A\<in>FinPow(X)" using assms(3).
  {
    fix B assume b:"B\<in>FinPow(X)" "B\<notin>\<FF>"
    {
      fix s assume s:"s\<in>X"
      {
        assume cont:"B\<union>{s}\<in>\<FF>"
        {
          assume "B=0"
          then have "B\<union>{s} = {s}" by auto
          with s assms(2) cont have False by auto
        } moreover
        {
          assume "B\<noteq>0"
          with b have "X-B \<in>\<FF>" using assms(1) set_ultrafilter[of B X \<FF>]
            unfolding FinPow_def by auto moreover
          from assms(1,2) s have "X-{s}\<in>\<FF>" using set_ultrafilter[of "{s}" X \<FF>]
            by auto
          ultimately have "(X-B)\<inter>(X-{s}) \<in>\<FF>" using assms(1)
            unfolding IsUltrafilter_def IsFilter_def by auto moreover
          {
            fix q assume "q\<in>(X-B)\<inter>(X-{s})"
            then have "q:X" "q\<notin>B" "q\<notin>{s}" by auto
            then have "q\<in>X-(B\<union>{s})" by auto
          }
          then have "(X-B)\<inter>(X-{s}) \<subseteq> X-(B\<union>{s})" by auto moreover
          have "X-(B\<union>{s})\<in>Pow(X)" by auto
          ultimately have "X-(B\<union>{s}) \<in>\<FF>" using assms(1) unfolding IsFilter_def IsUltrafilter_def
            by blast
          with cont have "(X-(B\<union>{s}))\<inter>(B\<union>{s}):  \<FF>" using assms(1)
            unfolding IsFilter_def IsUltrafilter_def by auto moreover
          {
            fix q assume "q\<in>(X-(B\<union>{s}))\<inter>(B\<union>{s})"
            then have False by auto
          }
          then have "(X-(B\<union>{s}))\<inter>(B\<union>{s}) = 0" by auto
          ultimately have "0:  \<FF>" by auto
          with assms(1) have False unfolding IsUltrafilter_def IsFilter_def by auto
        }
        ultimately have False by auto
      }
      then have "B\<union>{s}\<notin>\<FF>" by auto
    }
    then have "\<forall>q\<in>X. B \<union> {q} \<notin> \<FF>" by auto
  }
  then show "\<forall>A\<in>FinPow(X). A \<notin> \<FF> \<longrightarrow> (\<forall>q\<in>X. A \<union> {q} \<notin> \<FF>)" by auto
qed

text\<open>The cofinite filter plays an important role in ultrafilters.\<close>

corollary ultrafilter_contains_cofinite:
  assumes "\<FF>{is an ultrafilter on}X" "\<forall>x\<in>X. {x}\<notin>\<FF>"
  shows "(CoFinite(X))-{0} \<subseteq> \<FF>"
proof
  fix S assume "S\<in>(CoFinite(X))-{0}"
  then have s:"S \<in> Pow(X)" "X - S \<prec> nat" "S\<noteq>0" unfolding CoCardinal_def Cofinite_def by auto
  then have "Finite(X-S)" using lesspoll_nat_is_Finite by auto
  then have "X-S\<in>FinPow(X)" unfolding FinPow_def by auto
  with ultrafilter_finite_set assms have "X-S\<notin>\<FF>" by auto
  with assms(1) show "S\<in>\<FF>" using set_ultrafilter s(1,3) by auto
qed

text\<open>An ultrafilter is free or principal.\<close>

corollary ultrafilter_principal_or_free:
  assumes "\<FF>{is an ultrafilter on}X"
  shows "\<Inter>\<FF> = 0 \<or> (\<exists>x\<in>X. \<Inter>\<FF> = {x})"
proof(safe)
  assume "\<not>(\<exists>x\<in>X. \<Inter>\<FF> = {x})"
  then have r:"\<forall>x\<in>X. \<Inter>\<FF>\<noteq>{x}" by auto
  {
    fix x assume x:"x:X" "{x}:\<FF>"
    from this(2) assms have "\<forall>C\<in>Pow(X). {x} \<subseteq> C \<longrightarrow> C \<in> \<FF>" 
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have s:"{C\<in>Pow(X). x\<in>C} \<subseteq> \<FF>" by auto moreover
    {
      fix q assume q:"q\<in>\<FF>" "x\<notin>q"
      from q(2) s x(1) have "X-q:\<FF>" by blast
      with q(1) have "(X-q)\<inter>q\<in>\<FF>" using assms unfolding IsUltrafilter_def IsFilter_def by auto
      moreover have "(X-q)\<inter>q = 0" by auto
      ultimately have "0:\<FF>" by auto
      with assms have False unfolding IsUltrafilter_def IsFilter_def by auto
    }
    then have "\<FF>\<subseteq>{C\<in>Pow(X). x\<in>C}" using assms unfolding IsUltrafilter_def IsFilter_def by auto
    with s have "\<FF>={C\<in>Pow(X). x\<in>C}" by auto
    then have "\<Inter>\<FF>={x}" using x(2) by auto
    with r x(1) have False by auto
  }
  then have "\<forall>x\<in>X. {x}\<notin>\<FF>" by auto
  then have sub:"(Cofinite(X))-{0} \<subseteq> \<FF>" using ultrafilter_contains_cofinite assms by auto moreover
  from assms have a:"X\<noteq>0" unfolding IsUltrafilter_def IsFilter_def by auto
  have b:"X \<in>(Cofinite(X))" using carr_open[of "Cofinite(X)"] 
      union_cocardinal[of nat X] CoCar_is_topology[OF InfCard_nat] unfolding Cofinite_def by auto
  from a b have "X\<in>(Cofinite(X))-{0}" by auto
  with sub have A:"\<Inter>\<FF> \<subseteq> \<Inter>((Cofinite(X))-{0})" by auto
  {
    fix q assume q:"q\<in>\<Inter>((Cofinite(X))-{0})"
    from a b have B:"\<Inter>((Cofinite(X))-{0}) \<subseteq> X" by auto
    with q have "q\<in>X" by auto
    then have "X-(X-{q}) = {q}" by auto
    then have "X-(X-{q})\<approx>1" using singleton_eqpoll_1 by auto
    then have "X-(X-{q}) \<prec> nat" using eq_lesspoll_trans n_lesspoll_nat[OF nat_1I] by auto
    then have cof:"X-{q}\<in>(Cofinite(X))" unfolding Cofinite_def CoCardinal_def by auto
    {
      assume "X-{q} = 0"
      then have "X={q}" using `q:X` by auto
      then have "\<Inter>\<FF> \<subseteq> {q}"  using assms unfolding IsUltrafilter_def IsFilter_def by auto
      with `q\<in>X` r have "\<Inter>\<FF> = 0" by blast
    } moreover
    {
      assume "X-{q} \<noteq> 0"
      with cof have "X-{q}\<in>(Cofinite(X)) -{0}" by auto
      then have "\<Inter>((Cofinite(X))-{0}) \<subseteq> X-{q}" by auto
      with q have False by auto
      then have "\<Inter>\<FF> = 0" by auto
    } ultimately
    have "\<Inter>\<FF> = 0" by auto
  }
  then have "\<Inter>\<FF>=0 \<or> \<Inter>((Cofinite(X))-{0}) = 0" by blast
  with A show "\<Inter>\<FF>=0" by auto
qed



end