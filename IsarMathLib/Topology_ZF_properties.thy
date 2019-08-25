(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2012 Daniel de la Concepcion

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

section \<open>Properties in Topology\<close>

theory Topology_ZF_properties imports Topology_ZF_examples Topology_ZF_examples_1

begin

text\<open>
  This theory deals with topological properties which make use of cardinals.
\<close>

subsection\<open>Properties of compactness\<close>

text\<open>It is already defined what is a compact topological space, but the is a
generalization which may be useful sometimes.\<close>

definition
  IsCompactOfCard ("_{is compact of cardinal}_ {in}_" 90)
  where "K{is compact of cardinal} Q{in}T \<equiv> (Card(Q) \<and> K \<subseteq> \<Union>T \<and> 
  (\<forall> M\<in>Pow(T). K \<subseteq> \<Union>M \<longrightarrow> (\<exists> N \<in> Pow(M). K \<subseteq> \<Union>N \<and> N\<prec>Q)))"

text\<open>The usual compact property is the one defined over the cardinal
of the natural numbers.\<close>

lemma Compact_is_card_nat:
  shows "K{is compact in}T \<longleftrightarrow> (K{is compact of cardinal} nat {in}T)"
proof
  {
    assume "K{is compact in}T"
    then have sub:"K \<subseteq> \<Union>T"  and reg:"(\<forall> M\<in>Pow(T). K \<subseteq> \<Union>M \<longrightarrow> (\<exists> N \<in> FinPow(M). K \<subseteq> \<Union>N))"
      using IsCompact_def by auto
    {
      fix M
      assume "M\<in>Pow(T)""K\<subseteq>\<Union>M"
      with reg obtain N where "N\<in>FinPow(M)" "K\<subseteq>\<Union>N" by blast
      then have "Finite(N)" using FinPow_def by auto
      then obtain n where A:"n\<in>nat""N \<approx>n" using Finite_def by auto
      from A(1) have "n\<prec>nat" using n_lesspoll_nat by auto
      with A(2) have "N\<lesssim>nat" using lesspoll_def eq_lepoll_trans by auto
      moreover
      {
        assume "N \<approx>nat"
        then have "nat \<approx> N" using eqpoll_sym by auto 
        with A(2) have "nat \<approx>n" using eqpoll_trans by blast
        then have "n \<approx>nat" using eqpoll_sym by auto
        with \<open>n\<prec>nat\<close> have "False" using lesspoll_def by auto
      }
      then have "~(N \<approx>nat)" by auto
      with calculation \<open>K\<subseteq>\<Union>N\<close>\<open>N\<in>FinPow(M)\<close> have "N\<prec>nat""K\<subseteq>\<Union>N""N\<in>Pow(M)" using lesspoll_def
        FinPow_def by auto
      hence "(\<exists> N \<in> Pow(M). K \<subseteq> \<Union>N \<and> N\<prec>nat)" by auto
    }
    with sub show "K{is compact of cardinal} nat {in}T" using IsCompactOfCard_def Card_nat by auto
  }
  {
    assume "(K{is compact of cardinal} nat {in}T)"
    then have sub:"K\<subseteq>\<Union>T" and reg:"(\<forall> M\<in>Pow(T). K \<subseteq> \<Union>M \<longrightarrow> (\<exists> N \<in> Pow(M). K \<subseteq> \<Union>N \<and> N\<prec>nat))"
      using IsCompactOfCard_def by auto
    {
      fix M
      assume "M\<in>Pow(T)""K\<subseteq>\<Union>M"
      with reg have "(\<exists> N \<in> Pow(M). K \<subseteq> \<Union>N \<and> N\<prec>nat)" by auto
      then obtain N where "N\<in>Pow(M)""K\<subseteq>\<Union>N""N\<prec>nat" by blast
      then have "N\<in>FinPow(M)""K\<subseteq>\<Union>N" using lesspoll_nat_is_Finite FinPow_def by auto
      hence "\<exists>N\<in>FinPow(M). K\<subseteq>\<Union>N" by auto
    }
    with sub show "K{is compact in}T" using IsCompact_def by auto
  }
qed

text\<open>Another property of this kind widely used is the Lindeloef property;
it is the one on the successor of the natural numbers.\<close>

definition
  IsLindeloef  ("_{is lindeloef in}_" 90) where
  "K {is lindeloef in} T\<equiv>K{is compact of cardinal}csucc(nat){in}T"

text\<open>It would be natural to think that every countable set with any topology
is Lindeloef; but this statement is not provable in ZF. The reason is that
to build a subcover, most of the time we need to \emph{choose} sets
from an infinite collection which cannot be done in ZF. Additional axioms are needed,
but strictly weaker than the axiom of choice.\<close>

text\<open>However, if the topology has not many open sets, then the topological
space is indeed compact.\<close>

theorem card_top_comp:
  assumes "Card(Q)" "T\<prec>Q" "K\<subseteq>\<Union>T"
  shows "(K){is compact of cardinal}Q{in}T"
proof-
  {      
    fix M assume M:"M\<subseteq>T" "K\<subseteq>\<Union>M"
    from M(1) assms(2) have "M\<prec>Q" using subset_imp_lepoll lesspoll_trans1 by blast
    with M(2) have "\<exists>N\<in>Pow(M). K\<subseteq>\<Union>N \<and> N\<prec>Q" by auto
  }
  with assms(1,3) show ?thesis unfolding IsCompactOfCard_def by auto
qed

text\<open>The union of two compact sets, is compact; of any cardinality.\<close>

theorem union_compact:
  assumes "K{is compact of cardinal}Q{in}T" "K1{is compact of cardinal}Q{in}T" "InfCard(Q)"
  shows "(K \<union> K1){is compact of cardinal}Q{in}T" unfolding IsCompactOfCard_def
proof(safe)
  from assms(1) show "Card(Q)" unfolding IsCompactOfCard_def by auto
  fix x assume "x\<in>K" then show "x\<in>\<Union>T" using assms(1) unfolding IsCompactOfCard_def by blast
next
  fix x assume "x\<in>K1" then show "x\<in>\<Union>T" using assms(2) unfolding IsCompactOfCard_def by blast
next
  fix M assume "M\<subseteq>T" "K\<union>K1\<subseteq>\<Union>M"
  then have "K\<subseteq>\<Union>M""K1\<subseteq>\<Union>M" by auto
  with \<open>M\<subseteq>T\<close> have "\<exists>N\<in>Pow(M). K \<subseteq> \<Union>N \<and> N \<prec> Q""\<exists>N\<in>Pow(M). K1 \<subseteq> \<Union>N \<and> N \<prec> Q" using assms unfolding IsCompactOfCard_def
    by auto
  then obtain NK NK1 where "NK\<in>Pow(M)""NK1\<in>Pow(M)""K \<subseteq> \<Union>NK""K1 \<subseteq> \<Union>NK1""NK \<prec> Q""NK1 \<prec> Q" by auto
  then have "NK\<union>NK1 \<prec> Q""K\<union>K1\<subseteq>\<Union>(NK\<union>NK1)""NK\<union>NK1\<in>Pow(M)" using assms(3) less_less_imp_un_less by auto
  then show "\<exists>N\<in>Pow(M). K\<union>K1\<subseteq>\<Union>N \<and> N\<prec>Q" by auto
qed

text\<open>If a set is compact of cardinality \<open>Q\<close> for some topology,
it is compact of cardinality \<open>Q\<close> for every coarser topology.\<close>

theorem compact_coarser:
  assumes "T1\<subseteq>T" and "\<Union>T1=\<Union>T" and "(K){is compact of cardinal}Q{in}T"
  shows "(K){is compact of cardinal}Q{in}T1"
proof-
  {
    fix M
    assume AS:"M\<in>Pow(T1)""K\<subseteq>\<Union>M"
    then have "M\<in>Pow(T)""K\<subseteq>\<Union>M" using assms(1) by auto
    then have "\<exists>N\<in>Pow(M).K\<subseteq>\<Union>N\<and>N\<prec>Q" using assms(3) unfolding IsCompactOfCard_def by auto
  }
  then show "(K){is compact of cardinal}Q{in}T1" using assms(3,2) unfolding IsCompactOfCard_def by auto
qed

text\<open>If some set is compact for some cardinal, it is compact for any greater cardinal.\<close>

theorem compact_greater_card:
  assumes "Q\<lesssim>Q1" and "(K){is compact of cardinal}Q{in}T" and "Card(Q1)"
  shows "(K){is compact of cardinal}Q1{in}T"
proof-
  {
    fix M
    assume AS: "M\<in>Pow(T)""K\<subseteq>\<Union>M"
    then have "\<exists>N\<in>Pow(M).K\<subseteq>\<Union>N\<and>N\<prec>Q" using assms(2) unfolding IsCompactOfCard_def by auto
    then have "\<exists>N\<in>Pow(M).K\<subseteq>\<Union>N\<and>N\<prec>Q1" using assms(1) lesspoll_trans2
      unfolding IsCompactOfCard_def by auto
  }
  then show ?thesis using assms(2,3) unfolding IsCompactOfCard_def by auto
qed

text\<open>A closed subspace of a compact space of any cardinality, is also
compact of the same cardinality.\<close>

theorem compact_closed:
  assumes "K {is compact of cardinal} Q {in} T"
    and "R {is closed in} T"
  shows "(K\<inter>R) {is compact of cardinal} Q {in} T"
proof-
  {
    fix M
    assume AS:"M\<in>Pow(T)""K\<inter>R\<subseteq>\<Union>M"
    have "\<Union>T-R\<in>T" using assms(2) IsClosed_def by auto
    have "K-R\<subseteq>(\<Union>T-R)" using assms(1) IsCompactOfCard_def by auto
    with \<open>\<Union>T-R\<in>T\<close> have "K\<subseteq>\<Union>(M \<union>{\<Union>T-R})" and "M \<union>{\<Union>T-R}\<in>Pow(T)"
    proof (safe)
      {
        fix x
        assume "x\<in>M"
        with AS(1) show "x\<in>T" by auto
      }
      {
        fix x
        assume "x\<in>K"
        have "x\<in>R\<or>x\<notin>R" by auto
        with \<open>x\<in>K\<close> have "x\<in>K\<inter>R\<or>x\<in>K-R" by auto
        with AS(2) \<open>K-R\<subseteq>(\<Union>T-R)\<close> have "x\<in>\<Union>M\<or>x\<in>(\<Union>T-R)" by auto
        then show "x\<in>\<Union>(M \<union>{\<Union>T-R})" by auto
      }
    qed
    with assms(1) have "\<exists>N\<in>Pow(M\<union>{\<Union>T-R}). K \<subseteq> \<Union>N \<and> N \<prec> Q" unfolding IsCompactOfCard_def by auto
    then obtain N where cub:"N\<in>Pow(M\<union>{\<Union>T-R})" "K\<subseteq>\<Union>N" "N\<prec>Q" by auto
    have "N-{\<Union>T-R}\<in>Pow(M)""K\<inter>R\<subseteq>\<Union>(N-{\<Union>T-R})" "N-{\<Union>T-R}\<prec>Q"
    proof (safe)
      {
        fix x
        assume "x\<in>N""x\<notin>M"
        then show "x=\<Union>T-R" using cub(1) by auto
      }
      {
        fix x
        assume "x\<in>K""x\<in>R"
        then have "x\<notin>\<Union>T-R""x\<in>K" by auto
        then show "x\<in>\<Union>(N-{\<Union>T-R})" using cub(2) by blast
      }
      have "N-{\<Union>T-R}\<subseteq>N" by auto
      with cub(3) show "N-{\<Union>T-R}\<prec>Q" using subset_imp_lepoll lesspoll_trans1 by blast
    qed
    then have "\<exists>N\<in>Pow(M). K\<inter>R\<subseteq>\<Union>N \<and> N\<prec>Q" by auto
  }
  then have "\<forall>M\<in>Pow(T). (K \<inter> R \<subseteq> \<Union>M \<longrightarrow> (\<exists>N\<in>Pow(M). K \<inter> R \<subseteq> \<Union>N \<and> N \<prec> Q))" by auto
  then show ?thesis using IsCompactOfCard_def assms(1) by auto
qed

subsection\<open>Properties of numerability\<close>

text\<open>The properties of numerability deal with cardinals of some sets
built from the topology. The properties which are normally used
are the ones related to the cardinal of the natural numbers or its successor.\<close>

definition
  IsFirstOfCard ("_ {is of first type of cardinal}_" 90) where
  "(T {is of first type of cardinal} Q) \<equiv> \<forall>x\<in>\<Union>T. (\<exists>B. (B {is a base for} T) \<and> ({b\<in>B. x\<in>b} \<prec> Q))"

definition
  IsSecondOfCard ("_ {is of second type of cardinal}_" 90) where
  "(T {is of second type of cardinal}Q) \<equiv> (\<exists>B. (B {is a base for} T) \<and> (B \<prec> Q))"

definition
  IsSeparableOfCard ("_{is separable of cardinal}_" 90) where
  "T{is separable of cardinal}Q\<equiv> \<exists>U\<in>Pow(\<Union>T). Closure(U,T)=\<Union>T \<and> U\<prec>Q"

definition
  IsFirstCountable ("_ {is first countable}" 90) where
  "(T {is first countable}) \<equiv> T {is of first type of cardinal} csucc(nat)"

definition
  IsSecondCountable ("_ {is second countable}" 90) where
  "(T {is second countable}) \<equiv> (T {is of second type of cardinal}csucc(nat))"

definition
  IsSeparable ("_{is separable}" 90) where
  "T{is separable}\<equiv> T{is separable of cardinal}csucc(nat)"

text\<open>If a set is of second type of cardinal \<open>Q\<close>, then it is of
first type of that same cardinal.\<close>

theorem second_imp_first:
  assumes "T{is of second type of cardinal}Q"
  shows "T{is of first type of cardinal}Q"
proof-
  from assms have "\<exists>B. (B {is a base for} T) \<and> (B \<prec> Q)" using IsSecondOfCard_def by auto
  then obtain B where base:"(B {is a base for} T) \<and> (B \<prec> Q)" by auto
  {
    fix x
    assume "x\<in>\<Union>T"
    have "{b\<in>B. x\<in>b}\<subseteq>B" by auto
    then have "{b\<in>B. x\<in>b}\<lesssim>B" using subset_imp_lepoll by auto
    with base have "{b\<in>B. x\<in>b}\<prec>Q" using lesspoll_trans1 by auto
    with base have "(B {is a base for} T) \<and> {b\<in>B. x\<in>b}\<prec>Q" by auto
  }
  then have "\<forall>x\<in>\<Union>T. \<exists>B. (B {is a base for} T) \<and> {b\<in>B. x\<in>b}\<prec>Q" by auto
  then show ?thesis using IsFirstOfCard_def by auto
qed

text\<open>A set is dense iff it intersects all non-empty, open sets of the topology.\<close>

lemma dense_int_open:
  assumes "T{is a topology}" and "A\<subseteq>\<Union>T"
  shows "Closure(A,T)=\<Union>T \<longleftrightarrow> (\<forall>U\<in>T. U\<noteq>0 \<longrightarrow> A\<inter>U\<noteq>0)"
proof
  assume AS:"Closure(A,T)=\<Union>T"
  {
    fix U
    assume Uopen:"U\<in>T" and "U\<noteq>0"
    then have "U\<inter>\<Union>T\<noteq>0" by auto
    with AS have "U\<inter>Closure(A,T) \<noteq>0" by auto
    with assms Uopen have "U\<inter>A\<noteq>0" using topology0.cl_inter_neigh topology0_def by blast
  }
  then show "\<forall>U\<in>T. U\<noteq>0 \<longrightarrow> A\<inter>U\<noteq>0" by auto
  next
  assume AS:"\<forall>U\<in>T. U\<noteq>0 \<longrightarrow> A\<inter>U\<noteq>0"
  {
    fix x
    assume A:"x\<in>\<Union>T"
    then have "\<forall>U\<in>T. x\<in>U \<longrightarrow> U\<inter>A\<noteq>0" using AS by auto
    with assms A have "x\<in>Closure(A,T)" using topology0.inter_neigh_cl topology0_def by auto
  }
  then have "\<Union>T\<subseteq>Closure(A,T)" by auto
  with assms show "Closure(A,T)=\<Union>T" using topology0.Top_3_L11(1) topology0_def by blast
qed

subsection\<open>Relations between numerability properties and choice principles\<close>

text\<open>It is known that some statements in topology aren't just derived from
choice axioms, but also equivalent to them. Here is an example

The following are equivalent:
\begin{itemize}
\item Every topological space of second cardinality \<open>csucc(Q)\<close> is
separable of cardinality \<open>csucc(Q)\<close>.
\item The axiom of \<open>Q\<close> choice.
\end{itemize}

In the article \cite{HH1} there is a proof of this statement
for \<open>Q\<close>$=\mathbb{N}$, with more equivalences.\<close>

text\<open>If a topology is of second type of cardinal \<open>csucc(Q)\<close>, then it is separable
of the same cardinal. This result makes use of the axiom of choice for the cardinal
 \<open>Q\<close> on subsets of \<open>\<Union>T\<close>.\<close>

theorem Q_choice_imp_second_imp_separable:
  assumes "T{is of second type of cardinal}csucc(Q)" 
    and "{the axiom of} Q {choice holds for subsets} \<Union>T"
    and "T{is a topology}"
  shows "T{is separable of cardinal}csucc(Q)"
proof-
  from assms(1) have "\<exists>B. (B {is a base for} T) \<and> (B \<prec> csucc(Q))" using IsSecondOfCard_def by auto
  then obtain B where base:"(B {is a base for} T) \<and> (B \<prec> csucc(Q))" by auto
  let ?N="\<lambda>b\<in>B. b"
  let ?B="B-{0}"
  have "B-{0}\<subseteq>B" by auto
  with base have prec:"B-{0}\<prec>csucc(Q)" using subset_imp_lepoll lesspoll_trans1 by blast
  from base have baseOpen:"\<forall>b\<in>B. ?N`b\<in>T" using base_sets_open by auto
  from assms(2) have car:"Card(Q)" and reg:"(\<forall> M N. (M \<lesssim>Q \<and>  (\<forall>t\<in>M. N`t\<noteq>0 \<and> N`t\<subseteq>\<Union>T)) \<longrightarrow> (\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t)))"
  using AxiomCardinalChoice_def by auto
  then have "(?B \<lesssim>Q \<and>  (\<forall>t\<in>?B. ?N`t\<noteq>0 \<and> ?N`t\<subseteq>\<Union>T)) \<longrightarrow> (\<exists>f. f:Pi(?B,\<lambda>t. ?N`t) \<and> (\<forall>t\<in>?B. f`t\<in>?N`t))" by blast
  with prec have "(\<forall>t\<in>?B. ?N`t\<subseteq>\<Union>T) \<longrightarrow> (\<exists>f. f:Pi(?B,\<lambda>t. ?N`t) \<and> (\<forall>t\<in>?B. f`t\<in>?N`t))" using Card_less_csucc_eq_le car by auto
  with baseOpen have "\<exists>f. f:Pi(?B,\<lambda>t. ?N`t) \<and> (\<forall>t\<in>?B. f`t\<in>?N`t)" by blast
  then obtain f where f:"f:Pi(?B,\<lambda>t. ?N`t)" and f2:"\<forall>t\<in>?B. f`t\<in>?N`t" by auto
  {
    fix U
    assume "U\<in>T" and "U\<noteq>0"
    then obtain b where A1:"b\<in>B-{0}" and "b\<subseteq>U" using Top_1_2_L1 base by blast
    with f2 have "f`b\<in>U" by auto
    with A1 have "{f`b. b\<in>?B}\<inter>U\<noteq>0" by auto
  }
  then have r:"\<forall>U\<in>T. U\<noteq>0 \<longrightarrow> {f`b. b\<in>?B}\<inter>U\<noteq>0" by auto
  have "{f`b. b\<in>?B}\<subseteq>\<Union>T" using f2 baseOpen by auto
  moreover
  with r have "Closure({f`b. b\<in>?B},T)=\<Union>T" using dense_int_open assms(3) by auto
  moreover
  have ffun:"f:?B\<rightarrow>range(f)" using f range_of_fun by auto
  then have "f\<in>surj(?B,range(f))" using fun_is_surj by auto
  then have des1:"range(f)\<lesssim>?B" using surj_fun_inv_2[of "f""?B""range(f)""Q"] prec Card_less_csucc_eq_le car
    Card_is_Ord by auto
  then have "{f`b. b\<in>?B}\<subseteq>range(f)" using apply_rangeI[OF ffun] by auto
  then have "{f`b. b\<in>?B}\<lesssim>range(f)" using subset_imp_lepoll by auto
  with des1 have "{f`b. b\<in>?B}\<lesssim>?B" using lepoll_trans by blast
  with prec have "{f`b. b\<in>?B}\<prec>csucc(Q)" using lesspoll_trans1 by auto
  ultimately show ?thesis using IsSeparableOfCard_def by auto
qed

text\<open>The next theorem resolves that the axiom of \<open>Q\<close> choice for subsets
of \<open>\<Union>T\<close> is necessary for second type spaces to be separable of the same cardinal
\<open>csucc(Q)\<close>.\<close>

theorem second_imp_separable_imp_Q_choice:
  assumes "\<forall>T. (T{is a topology} \<and> (T{is of second type of cardinal}csucc(Q))) \<longrightarrow> (T{is separable of cardinal}csucc(Q))" 
  and "Card(Q)"
  shows "{the axiom of} Q {choice holds}"
proof-
  {
    fix N M
    assume AS:"M \<lesssim>Q \<and>  (\<forall>t\<in>M. N`t\<noteq>0)"
    (* First we build a topology using N and M such that it is of 
    second type of cardinal csucc(Q). It will be a partition topology.*)
    then obtain h where inj:"h\<in>inj(M,Q)" using lepoll_def by auto
    then have bij:"converse(h):bij(range(h),M)" using inj_bij_range bij_converse_bij by auto
    let ?T="{(N`(converse(h)`i))\<times>{i}. i\<in>range(h)}"
    {
      fix j
      assume AS2:"j\<in>range(h)"
      from bij have "converse(h):range(h)\<rightarrow>M" using bij_def inj_def by auto
      with AS2 have "converse(h)`j\<in>M" by simp
      with AS have "N`(converse(h)`j)\<noteq>0" by auto
      then have "(N`(converse(h)`j))\<times>{j}\<noteq>0" by auto
    }
    then have noEmpty:"0\<notin>?T" by auto
    moreover
    {
      fix A B
      assume AS2:"A\<in>?T""B\<in>?T""A\<inter>B\<noteq>0"
      then obtain j t where A_def:"A=N`(converse(h)`j)\<times>{j}" and B_def:"B=N`(converse(h)`t)\<times>{t}"
        and Range:"j\<in>range(h)" "t\<in>range(h)" by auto
      from AS2(3) obtain x where "x\<in>A\<inter>B" by auto
      with A_def B_def have "j=t" by auto
      with A_def B_def have "A=B" by auto
    }
    then have "(\<forall>A\<in>?T. \<forall>B\<in>?T. A=B\<or> A\<inter>B=0)" by auto
    ultimately
    have Part:"?T {is a partition of} \<Union>?T" unfolding IsAPartition_def by auto
    let ?\<tau>="PTopology \<Union>?T ?T"
    from Part have top:"?\<tau> {is a topology}" and base:"?T {is a base for}?\<tau>"
      using Ptopology_is_a_topology by auto
    let ?f="{\<langle>i,(N`(converse(h)`i))\<times>{i}\<rangle>. i\<in>range(h)}" 
    have "?f:range(h)\<rightarrow>?T" using functionI[of "?f"] Pi_def by auto
    then have "?f\<in>surj(range(h),?T)" unfolding surj_def using apply_equality by auto
    moreover
    have "range(h)\<subseteq>Q" using inj unfolding inj_def range_def domain_def Pi_def by auto
    ultimately have "?T\<lesssim> Q" using surj_fun_inv[of "?f""range(h)""?T""Q"] assms(2) Card_is_Ord lepoll_trans
      subset_imp_lepoll by auto
    then have  "?T\<prec>csucc(Q)" using Card_less_csucc_eq_le assms(2) by auto
    with base have "(?\<tau>{is of second type of cardinal}csucc(Q))" using IsSecondOfCard_def by auto
    with top have "?\<tau>{is separable of cardinal}csucc(Q)" using assms(1) by auto
    then obtain D where sub:"D\<in>Pow(\<Union>?\<tau>)" and clos:"Closure(D,?\<tau>)=\<Union>?\<tau>" and cardd:"D\<prec>csucc(Q)"
      using IsSeparableOfCard_def by auto
    (*We now build a dense subset of D such that it has only one point in each
    basic set. The first coordinate of those points will give us a choice function.*)
    then have "D\<lesssim>Q" using Card_less_csucc_eq_le assms(2) by auto
    then obtain r where r:"r\<in>inj(D,Q)" using lepoll_def by auto
    then have bij2:"converse(r):bij(range(r),D)" using inj_bij_range bij_converse_bij by auto
    then have surj2:"converse(r):surj(range(r),D)" using bij_def by auto
    let ?R="\<lambda>i\<in>range(h). {j\<in>range(r). converse(r)`j\<in>((N`(converse(h)`i))\<times>{i})}"
    {
      fix i
      assume AS:"i\<in>range(h)"
      then have T:"(N`(converse(h)`i))\<times>{i}\<in>?T" by auto 
      then have P: "(N`(converse(h)`i))\<times>{i}\<in>?\<tau>" using base unfolding IsAbaseFor_def by blast
      with top sub clos have "\<forall>U\<in>?\<tau>. U\<noteq>0 \<longrightarrow> D\<inter>U\<noteq>0" using dense_int_open by auto
      with P have "(N`(converse(h)`i))\<times>{i}\<noteq>0 \<longrightarrow> D\<inter>(N`(converse(h)`i))\<times>{i}\<noteq>0" by auto
      with T noEmpty have "D\<inter>(N`(converse(h)`i))\<times>{i}\<noteq>0" by auto
      then obtain x where "x\<in>D" and px:"x\<in>(N`(converse(h)`i))\<times>{i}" by auto
      with surj2 obtain j where "j\<in>range(r)" and "converse(r)`j=x" unfolding surj_def by blast
      with px have "j\<in>{j\<in>range(r). converse(r)`j\<in>((N`(converse(h)`i))\<times>{i})}" by auto
      then have "?R`i\<noteq>0" using beta_if[of "range(h)" _ i] AS by auto
    }
    then have nonE:"\<forall>i\<in>range(h). ?R`i\<noteq>0" by auto
    {
      fix i j
      assume i:"i\<in>range(h)" and j:"j\<in>?R`i"
      from j i have "converse(r)`j\<in>((N`(converse(h)`i))\<times>{i})" using beta_if by auto
    }
    then have pp:"\<forall>i\<in>range(h). \<forall>j\<in>?R`i. converse(r)`j\<in>((N`(converse(h)`i))\<times>{i})" by auto
    let ?E="{\<langle>m,fst(converse(r)`(\<mu> j. j\<in>?R`(h`m)))\<rangle>. m\<in>M}"
    have ff:"function(?E)" unfolding function_def by auto
    moreover
    (*We now have to prove that ?E is a choice function for M and N*)
    {
      fix m
      assume M:"m\<in>M"
      with inj have hm:"h`m\<in>range(h)" using apply_rangeI inj_def by auto
      {
        fix j
        assume "j\<in>?R`(h`m)"
        with hm have "j\<in>range(r)" using beta_if by auto
        from r have "r:surj(D,range(r))" using fun_is_surj inj_def by auto
        with \<open>j\<in>range(r)\<close> obtain d where "d\<in>D" and "r`d=j" using surj_def by auto
        then have "j\<in>Q" using r inj_def by auto
      }
      then have subcar:"?R`(h`m)\<subseteq>Q" by blast
      from nonE hm obtain ee where P:"ee\<in>?R`(h`m)" by blast
      with subcar have "ee\<in>Q" by auto
      then have "Ord(ee)" using assms(2) Card_is_Ord Ord_in_Ord by auto
      with P have "(\<mu> j. j\<in>?R`(h`m))\<in>?R`(h`m)" using LeastI[where i=ee and P="\<lambda>j. j\<in>?R`(h`m)"]
      by auto
      with pp hm have "converse(r)`(\<mu> j. j\<in>?R`(h`m))\<in>((N`(converse(h)`(h`m)))\<times>{(h`m)})" by auto
      then have "converse(r)`(\<mu> j. j\<in>?R`(h`m))\<in>((N`(m))\<times>{(h`m)})" using left_inverse[OF inj M]
        by simp
      then have "fst(converse(r)`(\<mu> j. j\<in>?R`(h`m)))\<in>(N`(m))" by auto
      }
    ultimately have thesis1:"\<forall>m\<in>M. ?E`m\<in>(N`(m))" using function_apply_equality by auto
    {
      fix e
      assume "e\<in>?E"
      then obtain m where "m\<in>M" and "e=\<langle>m,?E`m\<rangle>" using function_apply_equality ff by auto
      with thesis1 have "e\<in>Sigma(M,\<lambda>t. N`t)" by auto
    }
    then have "?E\<in>Pow(Sigma(M,\<lambda>t. N`t))" by auto
    with ff have "?E\<in>Pi(M,\<lambda>m. N`m)" using Pi_iff by auto
    then have "(\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t))" using thesis1 by auto
  }
  then show ?thesis using AxiomCardinalChoiceGen_def assms(2) by auto
qed

text\<open>Here is the equivalence from the two previous results.\<close>

theorem Q_choice_eq_secon_imp_sepa:
  assumes "Card(Q)"
  shows "(\<forall>T. (T{is a topology} \<and> (T{is of second type of cardinal}csucc(Q))) \<longrightarrow> (T{is separable of cardinal}csucc(Q)))
    \<longleftrightarrow>({the axiom of} Q {choice holds})"
  using Q_choice_imp_second_imp_separable choice_subset_imp_choice
  using second_imp_separable_imp_Q_choice assms by auto

text\<open>Given a base injective with a set, then we can find a
base whose elements are indexed by that set.\<close>

lemma base_to_indexed_base:
  assumes "B \<lesssim>Q" "B {is a base for}T"
  shows "\<exists>N. {N`i. i\<in>Q}{is a base for}T"
proof-
  from assms obtain f where f_def:"f\<in>inj(B,Q)" unfolding lepoll_def by auto
  let ?ff="{\<langle>b,f`b\<rangle>. b\<in>B}"
  have "domain(?ff)=B" by auto
  moreover
  have "relation(?ff)" unfolding relation_def by auto
  moreover
  have "function(?ff)" unfolding function_def by auto
  ultimately
  have fun:"?ff:B\<rightarrow>range(?ff)" using function_imp_Pi[of "?ff"] by auto
  then have injj:"?ff\<in>inj(B,range(?ff))" unfolding inj_def
  proof
    {
      fix w x
      assume AS:"w\<in>B""x\<in>B""{\<langle>b, f ` b\<rangle> . b \<in> B} ` w = {\<langle>b, f ` b\<rangle> . b \<in> B} ` x"
      then have "f`w=f`x" using apply_equality[OF _ fun] by auto
      then have "w=x" using f_def inj_def AS(1,2) by auto
    }
    then show "\<forall>w\<in>B. \<forall>x\<in>B. {\<langle>b, f ` b\<rangle> . b \<in> B} ` w = {\<langle>b, f ` b\<rangle> . b \<in> B} ` x \<longrightarrow> w = x" by auto
  qed
  then have bij:"?ff\<in>bij(B,range(?ff))" using inj_bij_range by auto
  from fun have "range(?ff)={f`b. b\<in>B}" by auto
  with f_def have ran:"range(?ff)\<subseteq>Q" using inj_def by auto
  let ?N="{\<langle>i,(if i\<in>range(?ff) then converse(?ff)`i else 0)\<rangle>. i\<in>Q}"
  have FN:"function(?N)" unfolding function_def by auto
  have "B \<subseteq>{?N`i. i\<in>Q}"
  proof
    fix t
    assume a:"t\<in>B"
    from bij have rr:"?ff:B\<rightarrow>range(?ff)" unfolding bij_def inj_def by auto
    have ig:"?ff`t=f`t" using a apply_equality[OF _ rr] by auto
    have r:"?ff`t\<in>range(?ff)" using apply_type[OF rr a].
    from ig have t:"?ff`t\<in>Q" using apply_type[OF _ a] f_def unfolding inj_def by auto
    with r have "?N`(?ff`t)=converse(?ff)`(?ff`t)" using function_apply_equality[OF _ FN] by auto
    then have "?N`(?ff`t)=t" using left_inverse[OF injj a] by auto
    then have "t=?N`(?ff`t)" by auto
    then have "\<exists>i\<in>Q. t=?N`i" using t(1) by auto
    then show "t\<in>{?N`i. i\<in>Q}" by simp
  qed
  moreover
  have "\<forall>r\<in>{?N`i. i\<in>Q}-B. r=0"
  proof
    fix r
    assume "r\<in>{?N`i. i\<in>Q}-B"
    then obtain j where R:"j\<in>Q""r=?N`j""r\<notin>B" by auto
    {
      assume AS:"j\<in>range(?ff)"
      with R(1) have "?N`j=converse(?ff)`j" using function_apply_equality[OF _ FN] by auto
      then have "?N`j\<in>B" using  apply_funtype[OF inj_is_fun[OF bij_is_inj[OF bij_converse_bij[OF bij]]] AS]
      by auto
      then have "False" using R(3,2) by auto
    }
    then have "j\<notin>range(?ff)" by auto
    then show "r=0" using function_apply_equality[OF _ FN] R(1,2) by auto
  qed
  ultimately have "{?N`i. i\<in>Q}=B\<or>{?N`i. i\<in>Q}=B \<union>{0}" by blast
  moreover
  have "(B \<union>{0})-{0}=B-{0}" by blast
  then have "(B \<union>{0})-{0} {is a base for}T" using base_no_0[of "B""T"] assms(2) by auto
  then have "B \<union>{0} {is a base for}T" using base_no_0[of "B \<union>{0}""T"] by auto
  ultimately
  have "{?N`i. i\<in>Q}{is a base for}T" using assms(2) by auto
  then show ?thesis by auto
qed

subsection\<open>Relation between numerability and compactness\<close>  

text\<open>If the axiom of \<open>Q\<close> choice holds, then any topology
of second type of cardinal \<open>csucc(Q)\<close> is compact of cardinal \<open>csucc(Q)\<close>\<close>

theorem compact_of_cardinal_Q:
  assumes "{the axiom of} Q {choice holds for subsets} (Pow(Q))"
    "T{is of second type of cardinal}csucc(Q)"
    "T{is a topology}"
  shows "((\<Union>T){is compact of cardinal}csucc(Q){in}T)"
proof-
  from assms(1) have CC:"Card(Q)" and reg:"\<And> M N. (M \<lesssim>Q \<and> (\<forall>t\<in>M. N`t\<noteq>0\<and>N`t\<subseteq>Pow(Q))) \<longrightarrow> (\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t))" using
  AxiomCardinalChoice_def by auto
  from assms(2) obtain R where "R\<lesssim>Q""R{is a base for}T" unfolding IsSecondOfCard_def using Card_less_csucc_eq_le CC by auto
  with base_to_indexed_base obtain N where base:"{N`i. i\<in>Q}{is a base for}T"  by blast
  {
    fix M
    assume A:"\<Union>T\<subseteq>\<Union>M""M\<in>Pow(T)"
    let ?\<alpha>="\<lambda>U\<in>M. {i\<in>Q. N`(i)\<subseteq>U}"
    have inj:"?\<alpha>\<in>inj(M,Pow(Q))" unfolding inj_def
    proof
    {
      show "(\<lambda>U\<in>M. {i \<in> Q . N ` i \<subseteq> U}) \<in> M \<rightarrow> Pow(Q)" using lam_type[of "M""\<lambda>U. {i \<in> Q . N`(i) \<subseteq> U}""%t. Pow(Q)"] by auto
      {
        fix w x
        assume AS:"w\<in>M""x\<in>M""{i \<in> Q . N`(i) \<subseteq> w} = {i \<in> Q . N`(i) \<subseteq> x}"
        from AS(1,2) A(2) have "w\<in>T""x\<in>T" by auto
        then have "w=Interior(w,T)""x=Interior(x,T)" using assms(3) topology0.Top_2_L3[of "T"]
          topology0_def[of "T"] by auto
        then have UN:"w=(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>w})""x=(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>x})"
          using interior_set_base_topology assms(3) base by auto
        {
          fix b
          assume "b\<in>w"
          then have "b\<in>\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>w}" using UN(1) by auto
          then obtain S where S:"S\<in>{N`(i). i\<in>Q}" "b\<in>S" "S\<subseteq>w" by blast
          then obtain j where j:"j\<in>Q""S=N`(j)" by auto
          then have "j\<in>{i \<in> Q . N`(i) \<subseteq> w}" using S(3) by auto
          then have "N`(j)\<subseteq>x""b\<in>N`(j)""j\<in>Q" using S(2) AS(3) j by auto
          then have "b\<in>(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>x})" by auto
          then have "b\<in>x" using UN(2) by auto
        }
        moreover
        {
          fix b
          assume "b\<in>x"
          then have "b\<in>\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>x}" using UN(2) by auto
          then obtain S where S:"S\<in>{N`(i). i\<in>Q}" "b\<in>S" "S\<subseteq>x" by blast
          then obtain j where j:"j\<in>Q""S=N`(j)" by auto
          then have "j\<in>{i \<in> Q . N`(i) \<subseteq> x}" using S(3) by auto
          then have "j\<in>{i \<in> Q . N`(i) \<subseteq> w}" using AS(3) by auto
          then have "N`(j)\<subseteq>w""b\<in>N`(j)""j\<in>Q" using S(2) j(2) by auto
          then have "b\<in>(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>w})" by auto
          then have "b\<in>w" using UN(2) by auto
        }
        ultimately have "w=x" by auto
      }
      then show "\<forall>w\<in>M. \<forall>x\<in>M. (\<lambda>U\<in>M. {i \<in> Q . N ` i \<subseteq> U}) ` w = (\<lambda>U\<in>M. {i \<in> Q . N ` i \<subseteq> U}) ` x \<longrightarrow> w = x" by auto
    }
    qed
    let ?X="\<lambda>i\<in>Q. {?\<alpha>`U. U\<in>{V\<in>M. N`(i)\<subseteq>V}}"
    let ?M="{i\<in>Q. ?X`i\<noteq>0}"
    have subMQ:"?M\<subseteq>Q" by auto
    then have ddd:"?M \<lesssim>Q" using subset_imp_lepoll by auto
    then have "?M \<lesssim>Q""\<forall>i\<in>?M. ?X`i\<noteq>0""\<forall>i\<in>?M. ?X`i\<subseteq>Pow(Q)" by auto
    then have "?M \<lesssim>Q""\<forall>i\<in>?M. ?X`i\<noteq>0""\<forall>i\<in>?M. ?X`i \<lesssim> Pow(Q)" using subset_imp_lepoll by auto
    then have "(\<exists>f. f:Pi(?M,\<lambda>t. ?X`t) \<and> (\<forall>t\<in>?M. f`t\<in>?X`t))" using reg[of "?M""?X"] by auto
    then obtain f where f:"f:Pi(?M,\<lambda>t. ?X`t)""(!!t. t\<in>?M \<Longrightarrow> f`t\<in>?X`t)" by auto
    {
      fix m
      assume S:"m\<in>?M"
      from f(2) S obtain YY where YY:"(YY\<in>M)" "(f`m=?\<alpha>`YY)" by auto
      then have Y:"(YY\<in>M)\<and>(f`m=?\<alpha>`YY)" by auto
      moreover
      { 
        fix U
        assume "U\<in>M\<and>(f`m=?\<alpha>`U)"
        then have "U=YY" using inj inj_def YY by auto
      }
      then have r:"\<And>x. x\<in>M\<and>(f`m=?\<alpha>`x) \<Longrightarrow> x=YY" by blast
      have "\<exists>!YY. YY\<in>M \<and> f`m=?\<alpha>`YY" using ex1I[of "%Y. Y\<in>M\<and> f`m=?\<alpha>`Y",OF Y r] by auto
    }
    then have ex1YY:"\<forall>m\<in>?M. \<exists>!YY. YY\<in>M \<and> f`m=?\<alpha>`YY" by auto
    let ?YYm="{\<langle>m,(THE YY. YY\<in>M \<and> f`m=?\<alpha>`YY)\<rangle>. m\<in>?M}"
    have aux:"\<And>m. m\<in>?M \<Longrightarrow> ?YYm`m=(THE YY. YY\<in>M \<and> f`m=?\<alpha>`YY)" unfolding apply_def by auto
    have ree:"\<forall>m\<in>?M. (?YYm`m)\<in>M \<and> f`m=?\<alpha>`(?YYm`m)"
    proof
      fix m
      assume C:"m\<in>?M"
      then have "\<exists>!YY. YY\<in>M \<and> f`m=?\<alpha>`YY" using ex1YY by auto
      then have "(THE YY. YY\<in>M \<and> f`m=?\<alpha>`YY)\<in>M\<and>f`m=?\<alpha>`(THE YY. YY\<in>M \<and> f`m=?\<alpha>`YY)"
        using theI[of "%Y. Y\<in>M\<and> f`m=?\<alpha>`Y"] by blast
      then show "(?YYm`m)\<in>M \<and> f`m=?\<alpha>`(?YYm`m)" apply (simp only: aux[OF C]) done
    qed
    have tt:"\<And>m. m\<in>?M \<Longrightarrow> N`(m)\<subseteq>?YYm`m"
    proof-
      fix m
      assume D:"m\<in>?M"
      then have QQ:"m\<in>Q" by auto
      from D have t:"(?YYm`m)\<in>M \<and> f`m=?\<alpha>`(?YYm`m)" using ree by blast
      then have "f`m=?\<alpha>`(?YYm`m)" by blast
      then have "(?\<alpha>`(?YYm`m))\<in>(\<lambda>i\<in>Q. {?\<alpha>`U. U\<in>{V\<in>M. N`(i)\<subseteq>V}})`m" using f(2)[OF D]
        by auto
      then have "(?\<alpha>`(?YYm`m))\<in>{?\<alpha>`U. U\<in>{V\<in>M. N`(m)\<subseteq>V}}" using QQ by auto
      then obtain U where "U\<in>{V\<in>M. N`(m)\<subseteq>V}""?\<alpha>`(?YYm`m)=?\<alpha>`U" by auto
      then have r:"U\<in>M""N`(m)\<subseteq>U""?\<alpha>`(?YYm`m)=?\<alpha>`U""(?YYm`m)\<in>M" using t by auto
      then have "?YYm`m=U" using  inj_apply_equality[OF inj] by blast
      then show "N`(m)\<subseteq>?YYm`m" using r by auto
    qed
    then have "(\<Union>m\<in>?M. N`(m))\<subseteq>(\<Union>m\<in>?M. ?YYm`m)"
    proof-
      {
        fix s
        assume "s\<in>(\<Union>m\<in>?M. N`(m))"
        then obtain t where r:"t\<in>?M""s\<in>N`(t)" by auto
        then have "s\<in>?YYm`t" using tt[OF r(1)] by blast
        then have "s\<in>(\<Union>m\<in>?M. ?YYm`m)" using r(1) by blast
      }
      then show ?thesis by blast
    qed
    moreover
    {
      fix x
      assume AT:"x\<in>\<Union>T"
      with A obtain U where BB:"U\<in>M""U\<in>T""x\<in>U" by auto
      then obtain j where BC:"j\<in>Q" "N`(j)\<subseteq>U""x\<in>N`(j)" using point_open_base_neigh[OF base,of "U""x"] by auto
      then have "?X`j\<noteq>0" using BB(1) by auto
      then have "j\<in>?M" using BC(1) by auto
      then have "x\<in>(\<Union>m\<in>?M. N`(m))" using BC(3) by auto
    }
    then have "\<Union>T\<subseteq>(\<Union>m\<in>?M. N`(m))" by blast
    ultimately have covers:"\<Union>T\<subseteq>(\<Union>m\<in>?M. ?YYm`m)" using subset_trans[of "\<Union>T""(\<Union>m\<in>?M. N`(m))""(\<Union>m\<in>?M. ?YYm`m)"]
      by auto
    have "relation(?YYm)" unfolding relation_def by auto
    moreover
    have f:"function(?YYm)" unfolding function_def by auto
    moreover
    have d:"domain(?YYm)=?M" by auto
    moreover
    have r:"range(?YYm)=?YYm``?M" by auto
    ultimately
    have fun:"?YYm:?M\<rightarrow>?YYm``?M" using function_imp_Pi[of "?YYm"] by auto
    have "?YYm\<in>surj(?M,?YYm``?M)" using fun_is_surj[OF fun] r by auto
    with surj_fun_inv[OF this subMQ Card_is_Ord[OF CC]]
    have "?YYm``?M \<lesssim> ?M" by auto
    with ddd have Rw:"?YYm``?M \<lesssim>Q" using lepoll_trans by blast
    {
      fix m assume "m\<in>?M"
      then have "\<langle>m,?YYm`m\<rangle>\<in>?YYm" using function_apply_Pair[OF f] d by blast
      then have "?YYm`m\<in>?YYm``?M" by auto}
      then have l1:"{?YYm`m. m\<in>?M}\<subseteq>?YYm``?M" by blast
      {
        fix t assume "t\<in>?YYm``?M"
        then have "\<exists>x\<in>?M. \<langle>x,t\<rangle>\<in>?YYm" unfolding image_def by auto
        then obtain r where S:"r\<in>?M""\<langle>r,t\<rangle>\<in>?YYm" by auto
        have "?YYm`r=t" using apply_equality[OF S(2) fun] by auto
        with S(1) have "t\<in>{?YYm`m. m\<in>?M}" by auto
      }
      with l1 have "{?YYm`m. m\<in>?M}=?YYm``?M" by blast
      with Rw have "{?YYm`m. m\<in>?M} \<lesssim>Q" by auto
      with covers have "{?YYm`m. m\<in>?M}\<in>Pow(M)\<and>\<Union>T\<subseteq>\<Union>{?YYm`m. m\<in>?M}\<and>{?YYm`m. m\<in>?M} \<prec>csucc(Q)" using ree 
        Card_less_csucc_eq_le[OF CC] by blast
      then have "\<exists>N\<in>Pow(M). \<Union>T\<subseteq>\<Union>N\<and>N\<prec>csucc(Q)" by auto
    }
  then have "\<forall>M\<in>Pow(T). \<Union>T \<subseteq> \<Union>M \<longrightarrow> (\<exists>N\<in>Pow(M). \<Union>T \<subseteq> \<Union>N \<and> N \<prec> csucc(Q))" by auto
  then show ?thesis using IsCompactOfCard_def Card_csucc CC Card_is_Ord by auto
qed

text\<open>In the following proof, we have chosen an infinite cardinal
to be able to apply the equation @{prop "Q\<times>Q\<approx>Q"}. For finite cardinals;
both, the assumption and the axiom of choice, are always true.\<close>

theorem second_imp_compact_imp_Q_choice_PowQ:
  assumes "\<forall>T. (T{is a topology} \<and> (T{is of second type of cardinal}csucc(Q))) \<longrightarrow> ((\<Union>T){is compact of cardinal}csucc(Q){in}T)" 
  and "InfCard(Q)"
  shows "{the axiom of} Q {choice holds for subsets} (Pow(Q))"
proof-
  {
    fix N M
    assume AS:"M \<lesssim>Q \<and>  (\<forall>t\<in>M. N`t\<noteq>0 \<and> N`t\<subseteq>Pow(Q))"
    then obtain h where "h\<in>inj(M,Q)" using lepoll_def by auto
    (* First we build a topology that it is of second type 
    of cardinal csucc(Q). It will be a discrete topology.*)
    have discTop:"Pow(Q\<times>M) {is a topology}" using Pow_is_top by auto
    {
      fix A
      assume AS:"A\<in>Pow(Q\<times>M)"
      have "A=\<Union>{{i}. i\<in>A}" by auto
      with AS have "\<exists>T\<in>Pow({{i}. i\<in>Q\<times>M}). A=\<Union>T" by auto
      then have "A\<in>{\<Union>U. U\<in>Pow({{i}. i\<in>Q\<times>M})}" by auto
    }
    moreover
    {
      fix A
      assume AS:"A\<in>{\<Union>U. U\<in>Pow({{i}. i\<in>Q\<times>M})}"
      then have "A\<in>Pow(Q\<times>M)" by auto
    }
    ultimately
    have base:"{{x}. x\<in>Q\<times>M} {is a base for} Pow(Q\<times>M)" unfolding IsAbaseFor_def by blast
    let ?f="{\<langle>i,{i}\<rangle>. i\<in>Q\<times>M}"
    have fff:"?f\<in>Q\<times>M\<rightarrow>{{i}. i\<in>Q\<times>M}" using Pi_def function_def by auto
    then have "?f\<in>inj(Q\<times>M,{{i}. i\<in>Q\<times>M})" unfolding inj_def using apply_equality by auto
    then have "?f\<in>bij(Q\<times>M,{{i}. i\<in>Q\<times>M})" unfolding bij_def surj_def  using fff
      apply_equality fff by auto
    then have "Q\<times>M\<approx>{{i}. i\<in>Q\<times>M}" using eqpoll_def by auto
    then have "{{i}. i\<in>Q\<times>M}\<approx>Q\<times>M" using eqpoll_sym by auto
    then have "{{i}. i\<in>Q\<times>M}\<lesssim>Q\<times>M" using eqpoll_imp_lepoll by auto
    then have "{{i}. i\<in>Q\<times>M}\<lesssim>Q\<times>Q" using AS prod_lepoll_mono[of "Q""Q""M""Q"] lepoll_refl[of "Q"]
      lepoll_trans by blast
    then have "{{i}. i\<in>Q\<times>M}\<lesssim>Q" using InfCard_square_eqpoll assms(2) lepoll_eq_trans by auto
    then have "{{i}. i\<in>Q\<times>M}\<prec>csucc(Q)" using Card_less_csucc_eq_le assms(2) InfCard_is_Card by auto
    then have "Pow(Q\<times>M) {is of second type of cardinal} csucc(Q)" using IsSecondOfCard_def base by auto
    then have comp:"(Q\<times>M) {is compact of cardinal}csucc(Q){in}Pow(Q\<times>M)" using discTop assms(1) by auto
    {
      fix W
      assume "W\<in>Pow(Q\<times>M)"
      then have T:"W{is closed in} Pow(Q\<times>M)" and "(Q\<times>M)\<inter>W=W" using IsClosed_def by auto
      with compact_closed[OF comp T] have "(W {is compact of cardinal}csucc(Q){in}Pow(Q\<times>M))" by auto
    }
    then have subCompact:"\<forall>W\<in>Pow(Q\<times>M). (W {is compact of cardinal}csucc(Q){in}Pow(Q\<times>M))" by auto
    let ?cub="\<Union>{{(U)\<times>{t}. U\<in>N`t}. t\<in>M}"
    from AS have "(\<Union>?cub)\<in>Pow((Q)\<times>M)" by auto
    with subCompact have Ncomp:"((\<Union>?cub) {is compact of cardinal}csucc(Q){in}Pow(Q\<times>M))" by auto
    have cond:"(?cub)\<in>Pow(Pow(Q\<times>M))\<and> \<Union>?cub\<subseteq>\<Union>?cub" using AS by auto
    have "\<exists>S\<in>Pow(?cub). (\<Union>?cub) \<subseteq> \<Union>S \<and> S \<prec> csucc(Q)"
    proof-
      {
        have "((\<Union>?cub) {is compact of cardinal}csucc(Q){in}Pow(Q\<times>M))" using Ncomp by auto
        then have "\<forall>M\<in>Pow(Pow(Q\<times>M)). \<Union>?cub \<subseteq> \<Union>M \<longrightarrow> (\<exists>Na\<in>Pow(M). \<Union>?cub \<subseteq> \<Union>Na \<and> Na \<prec> csucc(Q))" 
          unfolding IsCompactOfCard_def by auto
        with cond have "\<exists>S\<in>Pow(?cub). \<Union>?cub \<subseteq> \<Union>S \<and> S \<prec> csucc(Q)" by auto
      }
      then show ?thesis by auto
    qed
    then have ttt:"\<exists>S\<in>Pow(?cub). (\<Union>?cub) \<subseteq> \<Union>S \<and> S \<lesssim> Q" using Card_less_csucc_eq_le assms(2) InfCard_is_Card by auto
    then obtain S where S_def:"S\<in>Pow(?cub)""(\<Union>?cub) \<subseteq> \<Union>S" "S \<lesssim> Q" by auto
    {
      fix t
      assume AA:"t\<in>M""N`t\<noteq>{0}"
      from AA(1) AS have "N`t\<noteq>0" by auto
      with AA(2) obtain U where G:"U\<in>N`t" and notEm:"U\<noteq>0" by blast
      then have "U\<times>{t}\<in>?cub" using AA by auto
      then have "U\<times>{t}\<subseteq>\<Union>?cub" by auto
      with G notEm AA have "\<exists>s. \<langle>s,t\<rangle>\<in>\<Union>?cub" by auto
    }
    then have "\<forall>t\<in>M. (N`t\<noteq>{0})\<longrightarrow> (\<exists>s. \<langle>s,t\<rangle>\<in>\<Union>?cub)" by auto
    then have A:"\<forall>t\<in>M. (N`t\<noteq>{0})\<longrightarrow> (\<exists>s. \<langle>s,t\<rangle>\<in>\<Union>S)" using S_def(2) by blast
    from S_def(1) have B:"\<forall>f\<in>S. \<exists>t\<in>M. \<exists>U\<in>N`t. f=U\<times>{t}" by blast
    from A B have "\<forall>t\<in>M. (N`t\<noteq>{0})\<longrightarrow> (\<exists>U\<in>N`t. U\<times>{t}\<in>S)" by blast
    then have noEmp:"\<forall>t\<in>M. (N`t\<noteq>{0})\<longrightarrow> (S\<inter>({U\<times>{t}. U\<in>N`t})\<noteq>0)" by auto
    from S_def(3) obtain r where r:"r:inj(S,Q)" using lepoll_def by auto
    then have bij2:"converse(r):bij(range(r),S)" using inj_bij_range bij_converse_bij by auto
    then have surj2:"converse(r):surj(range(r),S)" using bij_def by auto
    let ?R="\<lambda>t\<in>M. {j\<in>range(r). converse(r)`j\<in>({U\<times>{t}. U\<in>N`t})}"
    {
      fix t
      assume AA:"t\<in>M""N`t\<noteq>{0}"
      then have "(S\<inter>({U\<times>{t}. U\<in>N`t})\<noteq>0)" using noEmp by auto
      then obtain s where ss:"s\<in>S""s\<in>{U\<times>{t}. U\<in>N`t}" by blast
      then obtain j where "converse(r)`j=s" "j\<in>range(r)" using surj2 unfolding surj_def by blast
      then have "j\<in>{j\<in>range(r). converse(r)`j\<in>({U\<times>{t}. U\<in>N`t})}" using ss by auto
      then have "?R`t\<noteq>0" using beta_if AA by auto
    }
    then have nonE:"\<forall>t\<in>M. N`t\<noteq>{0}\<longrightarrow>?R`t\<noteq>0" by auto
    {
      fix t j
      assume "t\<in>M""j\<in>?R`t"
      then have "converse(r)`j\<in>{U\<times>{t}. U\<in>N`t}" using beta_if by auto
      }
    then have pp:"\<forall>t\<in>M. \<forall>j\<in>?R`t. converse(r)`j\<in>{U\<times>{t}. U\<in>N`t}" by auto
    have reg:"\<forall>t U V. U\<times>{t}=V\<times>{t}\<longrightarrow>U=V"
    proof-
      { 
        fix t U V
        assume AA:"U\<times>{t}=V\<times>{t}"
        {
          fix v
          assume "v\<in>V"
          then have "\<langle>v,t\<rangle>\<in>V \<times>{t}" by auto
          then have "\<langle>v,t\<rangle>\<in>U \<times>{t}" using AA by auto
          then have "v\<in>U" by auto
        }
        then have "V\<subseteq>U" by auto
        moreover
        {
          fix u
          assume "u\<in>U"
          then have "\<langle>u,t\<rangle>\<in>U \<times>{t}" by auto
          then have "\<langle>u,t\<rangle>\<in>V \<times>{t}" using AA by auto
          then have "u\<in>V" by auto
        }
        then have "U\<subseteq>V" by auto
        ultimately have "U=V" by auto
      }
      then show ?thesis by auto
    qed
    (*The last part is to prove that ?E is the choice function.*)
    let ?E="{\<langle>t,if N`t={0} then 0 else (THE U. converse(r)`(\<mu> j. j\<in>?R`t)=U\<times>{t})\<rangle>. t\<in>M}"
    have ff:"function(?E)" unfolding function_def by auto
    moreover
    {
      fix t
      assume pm:"t\<in>M"
       { assume nonEE:"N`t\<noteq>{0}"
      {
        fix j
        assume "j\<in>?R`t"
        with pm(1) have "j\<in>range(r)" using beta_if by auto
        from r have "r:surj(S,range(r))" using fun_is_surj inj_def by auto
        with \<open>j\<in>range(r)\<close> obtain d where "d\<in>S" and "r`d=j" using surj_def by auto
        then have "j\<in>Q" using r inj_def by auto
        }
      then have sub:"?R`t\<subseteq>Q" by blast
      from nonE pm nonEE obtain ee where P:"ee\<in>?R`t" by blast
      with sub have "ee\<in>Q" by auto
      then have "Ord(ee)" using assms(2) Card_is_Ord Ord_in_Ord InfCard_is_Card by blast
      with P have "(\<mu> j. j\<in>?R`t)\<in>?R`t" using LeastI[where i=ee and P="\<lambda>j. j\<in>?R`t"] by auto
      with pp pm have "converse(r)`(\<mu> j. j\<in>?R`t)\<in>{U\<times>{t}. U\<in>N`t}" by auto
      then obtain W where "converse(r)`(\<mu> j. j\<in>?R`t)=W\<times>{t}" and s:"W\<in>N`t" by auto
      then have "(THE U. converse(r)`(\<mu> j. j\<in>?R`t)=U\<times>{t})=W" using reg by auto
      with s have "(THE U. converse(r)`(\<mu> j. j\<in>?R`t)=U\<times>{t})\<in>N`t" by auto
    }
    then have "(if N`t={0} then 0 else (THE U. converse(r)`(\<mu> j. j\<in>?R`t)=U\<times>{t}))\<in>N`t" by auto
    }
    ultimately have thesis1:"\<forall>t\<in>M. ?E`t\<in>N`t" using function_apply_equality by auto
    {
      fix e
      assume "e\<in>?E"
      then obtain m where "m\<in>M" and "e=\<langle>m,?E`m\<rangle>" using function_apply_equality ff by auto
      with thesis1 have "e\<in>Sigma(M,\<lambda>t. N`t)" by auto
    }
    then have "?E\<in>Pow(Sigma(M,\<lambda>t. N`t))" by auto
    with ff have "?E\<in>Pi(M,\<lambda>m. N`m)" using Pi_iff by auto
    then have "(\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t))" using thesis1 by auto}
    then show ?thesis using AxiomCardinalChoice_def assms(2) InfCard_is_Card by auto
qed

text\<open>The two previous results, state the following equivalence:\<close>

theorem Q_choice_Pow_eq_secon_imp_comp:
  assumes "InfCard(Q)"
  shows  "(\<forall>T. (T{is a topology} \<and> (T{is of second type of cardinal}csucc(Q))) \<longrightarrow> ((\<Union>T){is compact of cardinal}csucc(Q){in}T))
    \<longleftrightarrow>({the axiom of} Q {choice holds for subsets} (Pow(Q)))"
    using second_imp_compact_imp_Q_choice_PowQ compact_of_cardinal_Q assms by auto

text\<open>In the next result we will prove that if the space $(\kappa,Pow(\kappa))$,
for $\kappa$ an infinite cardinal, is compact of its successor cardinal; then all
topologycal spaces which are of second type of the successor cardinal of $\kappa$
are also compact of that cardinal.\<close>

theorem Q_csuccQ_comp_eq_Q_choice_Pow:
  assumes "InfCard(Q)" "(Q){is compact of cardinal}csucc(Q){in}Pow(Q)"
  shows "\<forall>T. (T{is a topology} \<and> (T{is of second type of cardinal}csucc(Q))) \<longrightarrow> ((\<Union>T){is compact of cardinal}csucc(Q){in}T)"
proof
  fix T
  {
    assume top:"T {is a topology}" and sec:"T{is of second type of cardinal}csucc(Q)"
    from assms have "Card(csucc(Q))" "Card(Q)" using InfCard_is_Card Card_is_Ord Card_csucc by auto
    moreover
    have "\<Union>T\<subseteq>\<Union>T" by auto
    moreover
    {
      fix M
      assume MT:"M\<in>Pow(T)" and cover:"\<Union>T\<subseteq>\<Union>M"
      from sec obtain B where "B {is a base for} T" "B\<prec>csucc(Q)" using IsSecondOfCard_def by auto
      with \<open>Card(Q)\<close> obtain N where base:"{N`i. i\<in>Q}{is a base for}T" using Card_less_csucc_eq_le
        base_to_indexed_base by blast
      let ?S="{\<langle>u,{i\<in>Q. N`i\<subseteq>u}\<rangle>. u\<in>M}"
      have "function(?S)" unfolding function_def by auto
      then have "?S:M\<rightarrow>Pow(Q)" using Pi_iff by auto
      then have "?S\<in>inj(M,Pow(Q))" unfolding inj_def
        proof
        {
          fix w x
          assume AS:"w\<in>M""x\<in>M""{\<langle>u, {i \<in> Q . N ` i \<subseteq> u}\<rangle> . u \<in> M} ` w = {\<langle>u, {i \<in> Q . N ` i \<subseteq> u}\<rangle> . u \<in> M} ` x"
          with \<open>?S:M\<rightarrow>Pow(Q)\<close> have ASS:"{i \<in> Q . N ` i \<subseteq> w}={i \<in> Q . N ` i \<subseteq> x}" using apply_equality by auto
          from AS(1,2) MT have "w\<in>T""x\<in>T" by auto
          then have "w=Interior(w,T)""x=Interior(x,T)" using top topology0.Top_2_L3[of "T"]
            topology0_def[of "T"] by auto
          then have UN:"w=(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>w})""x=(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>x})"
            using interior_set_base_topology top base by auto
          {
            fix b
            assume "b\<in>w"
            then have "b\<in>\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>w}" using UN(1) by auto
            then obtain S where S:"S\<in>{N`(i). i\<in>Q}" "b\<in>S" "S\<subseteq>w" by blast
            then obtain j where j:"j\<in>Q""S=N`(j)" by auto
            then have "j\<in>{i \<in> Q . N`(i) \<subseteq> w}" using S(3) by auto
            then have "N`(j)\<subseteq>x""b\<in>N`(j)""j\<in>Q" using S(2) ASS j by auto
            then have "b\<in>(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>x})" by auto
            then have "b\<in>x" using UN(2) by auto
          }
          moreover
          {
            fix b
            assume "b\<in>x"
            then have "b\<in>\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>x}" using UN(2) by auto
            then obtain S where S:"S\<in>{N`(i). i\<in>Q}" "b\<in>S" "S\<subseteq>x" by blast
            then obtain j where j:"j\<in>Q""S=N`(j)" by auto
            then have "j\<in>{i \<in> Q . N`(i) \<subseteq> x}" using S(3) by auto
            then have "j\<in>{i \<in> Q . N`(i) \<subseteq> w}" using ASS by auto
            then have "N`(j)\<subseteq>w""b\<in>N`(j)""j\<in>Q" using S(2) j(2) by auto
            then have "b\<in>(\<Union>{B\<in>{N`(i). i\<in>Q}. B\<subseteq>w})" by auto
            then have "b\<in>w" using UN(2) by auto
          }
          ultimately have "w=x" by auto 
        }
        then show "\<forall>w\<in>M. \<forall>x\<in>M. {\<langle>u, {i \<in> Q . N ` i \<subseteq> u}\<rangle> . u \<in> M} ` w = {\<langle>u, {i \<in> Q . N ` i \<subseteq> u}\<rangle> . u \<in> M} ` x \<longrightarrow> w = x" by auto
      qed
      then have "?S\<in>bij(M,range(?S))" using fun_is_surj unfolding bij_def inj_def surj_def by force
      have "range(?S)\<subseteq>Pow(Q)" by auto
      then have "range(?S)\<in>Pow(Pow(Q))" by auto
      moreover
      have "(\<Union>(range(?S))) {is closed in} Pow(Q)" "Q\<inter>(\<Union>range(?S))=(\<Union>range(?S))" using IsClosed_def by auto
      from this(2) compact_closed[OF assms(2) this(1)] have "(\<Union>range(?S)){is compact of cardinal}csucc(Q) {in}Pow(Q)"
        by auto
      moreover
      have "\<Union>(range(?S))\<subseteq>\<Union>(range(?S))" by auto
      ultimately have "\<exists>S\<in>Pow(range(?S)). (\<Union>(range(?S)))\<subseteq>\<Union>S \<and> S\<prec> csucc(Q)" using IsCompactOfCard_def by auto
      then obtain SS where SS_def:"SS\<subseteq>range(?S)" "(\<Union>(range(?S)))\<subseteq>\<Union>SS" "SS\<prec> csucc(Q)" by auto
      with \<open>?S\<in>bij(M,range(?S))\<close> have con:"converse(?S)\<in>bij(range(?S),M)" using bij_converse_bij by auto
      then have r1:"restrict(converse(?S),SS)\<in>bij(SS,converse(?S)``SS)" using restrict_bij bij_def SS_def(1) by auto
      then have rr:"converse(restrict(converse(?S),SS))\<in>bij(converse(?S)``SS,SS)" using bij_converse_bij by auto
      {
        fix x
        assume "x\<in>\<Union>T"
        with cover have "x\<in>\<Union>M" by auto
        then obtain R where "R\<in>M" "x\<in>R" by auto
        with MT have "R\<in>T" "x\<in>R" by auto
        then have "\<exists>V\<in>{N`i. i\<in>Q}. V\<subseteq>R \<and> x\<in>V" using point_open_base_neigh base by force
        then obtain j where "j\<in>Q" "N`j\<subseteq>R" and x_p:"x\<in>N`j" by auto
        with \<open>R\<in>M\<close> \<open>?S:M\<rightarrow>Pow(Q)\<close> \<open>?S\<in>bij(M,range(?S))\<close> have "?S`R\<in>range(?S) \<and> j\<in>?S`R" using apply_equality 
          bij_def inj_def by auto
        from exI[where P="\<lambda>t. t\<in>range(?S) \<and> j\<in>t", OF this] have "\<exists>A\<in>range(?S). j\<in>A" unfolding Bex_def
          by auto
        then have "j\<in>(\<Union>(range(?S)))" by auto
        then have "j\<in>\<Union>SS" using SS_def(2) by blast
        then obtain SR where "SR\<in>SS" "j\<in>SR" by auto
        moreover
        have "converse(restrict(converse(?S),SS))\<in>surj(converse(?S)``SS,SS)" using rr bij_def by auto
        ultimately obtain RR where "converse(restrict(converse(?S),SS))`RR=SR" and p:"RR\<in>converse(?S)``SS" unfolding surj_def by blast
        then have "converse(converse(restrict(converse(?S),SS)))`(converse(restrict(converse(?S),SS))`RR)=converse(converse(restrict(converse(?S),SS)))`SR"
          by auto
        moreover
        have "converse(restrict(converse(?S),SS))\<in>inj(converse(?S)``SS,SS)" using rr unfolding bij_def by auto
        moreover
        ultimately have "RR=converse(converse(restrict(converse(?S),SS)))`SR" using left_inverse[OF _ p]
          by force
        moreover
        with r1 have "restrict(converse(?S),SS)\<in>SS\<rightarrow>converse(?S)``SS" unfolding bij_def inj_def by auto
        then have "relation(restrict(converse(?S),SS))" using Pi_def relation_def by auto
        then have "converse(converse(restrict(converse(?S),SS)))=restrict(converse(?S),SS)" using relation_converse_converse by auto
        ultimately have "RR=restrict(converse(?S),SS)`SR" by auto
        with \<open>SR\<in>SS\<close> have eq:"RR=converse(?S)`SR" unfolding restrict by auto
        then have "converse(converse(?S))`RR=converse(converse(?S))`(converse(?S)`SR)" by auto
        moreover
        with \<open>SR\<in>SS\<close> have "SR\<in>range(?S)" using SS_def(1) by auto
        from con left_inverse[OF _ this] have "converse(converse(?S))`(converse(?S)`SR)=SR" unfolding bij_def
          by auto
        ultimately have "converse(converse(?S))`RR=SR" by auto
        then have "?S`RR=SR" using relation_converse_converse[of "?S"] unfolding relation_def by auto
        moreover
        have "converse(?S):range(?S)\<rightarrow>M" using con bij_def inj_def by auto
        with \<open>SR\<in>range(?S)\<close> have "converse(?S)`SR\<in>M" using apply_funtype
          by auto
        with eq have "RR\<in>M" by auto
        ultimately have "SR={i\<in>Q. N`i\<subseteq>RR}" using \<open>?S:M\<rightarrow>Pow(Q)\<close> apply_equality by auto
        then have "N`j\<subseteq>RR" using \<open>j\<in>SR\<close> by auto
        with x_p have "x\<in>RR" by auto
        with p have "x\<in>\<Union>(converse(?S)``SS)" by auto
      }
      then have "\<Union>T\<subseteq>\<Union>(converse(?S)``SS)" by blast
      moreover
      {
        from con have "converse(?S)``SS={converse(?S)`R. R\<in>SS}" using image_function[of "converse(?S)" "SS"]
          SS_def(1) unfolding range_def bij_def inj_def Pi_def by auto
        have "{converse(?S)`R. R\<in>SS}\<subseteq>{converse(?S)`R. R\<in>range(?S)}" using SS_def(1) by auto
        moreover
        have "converse(?S):range(?S)\<rightarrow>M" using con unfolding bij_def inj_def by auto
        then have "{converse(?S)`R. R\<in>range(?S)}\<subseteq>M" using apply_funtype by force
        ultimately
        have "(converse(?S)``SS)\<subseteq>M" by auto
      }
      then have "converse(?S)``SS\<in>Pow(M)" by auto
      moreover
      with rr have "converse(?S)``SS\<approx>SS" using eqpoll_def by auto
      then have "converse(?S)``SS\<prec>csucc(Q)" using SS_def(3) eq_lesspoll_trans by auto
      ultimately
      have "\<exists>N\<in>Pow(M). \<Union>T\<subseteq>\<Union>N \<and> N\<prec>csucc(Q)" by auto
    }
    then have "\<forall>M\<in>Pow(T). \<Union>T\<subseteq>\<Union>M \<longrightarrow> (\<exists>N\<in>Pow(M). \<Union>T\<subseteq>\<Union>N \<and> N\<prec>csucc(Q))" by auto
    ultimately have "(\<Union>T){is compact of cardinal}csucc(Q){in}T" unfolding IsCompactOfCard_def
      by auto
  }
  then show "(T {is a topology}) \<and> (T {is of second type of cardinal}csucc(Q)) \<longrightarrow> ((\<Union>T){is compact of cardinal}csucc(Q) {in}T)"
  by auto
qed

theorem Q_disc_is_second_card_csuccQ:
  assumes "InfCard(Q)" 
  shows "Pow(Q){is of second type of cardinal}csucc(Q)"
proof-
  {
    fix A
    assume AS:"A\<in>Pow(Q)"
    have "A=\<Union>{{i}. i\<in>A}" by auto
    with AS have "\<exists>T\<in>Pow({{i}. i\<in>Q}). A=\<Union>T" by auto
    then have "A\<in>{\<Union>U. U\<in>Pow({{i}. i\<in>Q})}" by auto
  }
  moreover
  {
    fix A
    assume AS:"A\<in>{\<Union>U. U\<in>Pow({{i}. i\<in>Q})}"
    then have "A\<in>Pow(Q)" by auto
  }
  ultimately
  have base:"{{x}. x\<in>Q} {is a base for} Pow(Q)" unfolding IsAbaseFor_def by blast
  let ?f="{\<langle>i,{i}\<rangle>. i\<in>Q}"
  have "?f\<in>Q\<rightarrow>{{x}. x\<in>Q}" unfolding Pi_def function_def by auto
  then have "?f\<in>inj(Q,{{x}. x\<in>Q})" unfolding inj_def using apply_equality by auto
  moreover
  from \<open>?f\<in>Q\<rightarrow>{{x}. x\<in>Q}\<close> have "?f\<in>surj(Q,{{x}. x\<in>Q})" unfolding surj_def using apply_equality
    by auto
  ultimately have "?f\<in>bij(Q,{{x}. x\<in>Q})" unfolding bij_def by auto
  then have "Q\<approx>{{x}. x\<in>Q}" using eqpoll_def by auto
  then have "{{x}. x\<in>Q}\<approx>Q" using eqpoll_sym by auto
  then have "{{x}. x\<in>Q}\<lesssim>Q" using eqpoll_imp_lepoll by auto
  then have "{{x}. x\<in>Q}\<prec>csucc(Q)" using Card_less_csucc_eq_le assms InfCard_is_Card by auto
  with base show ?thesis using IsSecondOfCard_def by auto
qed

text\<open>This previous results give us another equivalence of the axiom of \<open>Q\<close> choice
that is apparently weaker (easier to check) to the previous one.\<close>

theorem Q_disc_comp_csuccQ_eq_Q_choice_csuccQ:
  assumes "InfCard(Q)"
  shows "(Q{is compact of cardinal}csucc(Q){in}(Pow(Q))) \<longleftrightarrow> ({the axiom of}Q{choice holds for subsets}(Pow(Q)))"
  proof
  assume "Q{is compact of cardinal}csucc(Q) {in}Pow(Q)"
  with assms show "{the axiom of}Q{choice holds for subsets}(Pow(Q))" using Q_choice_Pow_eq_secon_imp_comp Q_csuccQ_comp_eq_Q_choice_Pow
    by auto
  next
  assume "{the axiom of}Q{choice holds for subsets}(Pow(Q))"
  with assms show "Q{is compact of cardinal}csucc(Q){in}(Pow(Q))" using Q_disc_is_second_card_csuccQ Q_choice_Pow_eq_secon_imp_comp Pow_is_top[of "Q"]
    by force
qed


end


