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

section \<open>Cardinal numbers\<close>

theory Cardinal_ZF imports ZF.CardinalArith Finite_ZF func1

begin

text\<open>This theory file deals with results on cardinal numbers (cardinals). Cardinals are
a genaralization of the natural numbers, used to measure the cardinality (size) of sets.
  Contributed by Daniel de la Concepcion.\<close>

subsection\<open>Some new ideas on cardinals\<close>

text\<open>All the results of this section are done without assuming
the Axiom of Choice. With the Axiom of Choice in play, the proofs become easier
and some of the assumptions may be dropped.

Since General Topology Theory is closely related to Set Theory, it is very interesting
to make use of all the possibilities of Set Theory to try to classify homeomorphic
topological spaces. These ideas are generally used to prove that two topological
spaces are not homeomorphic.\<close>

text\<open>There exist cardinals which are the successor of another cardinal,
but; as happens with ordinals, there are cardinals which are limit cardinal.\<close>

definition
    "LimitC(i) \<equiv> Card(i) \<and> 0<i \<and> (\<forall>y. (y<i\<and>Card(y)) \<longrightarrow> csucc(y)<i)"

text\<open>Simple fact used a couple of times in proofs.\<close>

lemma nat_less_infty: assumes "n\<in>nat" and "InfCard(X)" shows "n<X"
proof -
  from assms have "n<nat" and "nat\<le>X" using lt_def InfCard_def by auto
  then show "n<X" using lt_trans2 by blast
qed

text\<open>There are three types of cardinals, the zero one, the succesors
of other cardinals and the limit cardinals.\<close>

lemma Card_cases_disj: 
  assumes "Card(i)" 
  shows "i=0 | (\<exists>j. Card(j) \<and> i=csucc(j)) | LimitC(i)"
proof-
  from assms have D: "Ord(i)" using Card_is_Ord by auto
  {
    assume F: "i\<noteq>0"
    assume Contr: "~LimitC(i)"
    from F D have "0<i" using Ord_0_lt by auto
    with Contr assms have "\<exists>y. y < i \<and> Card(y) \<and> \<not> csucc(y) < i" 
      using LimitC_def by blast
    then obtain y where " y < i \<and> Card(y) \<and> \<not> csucc(y) < i"  by blast
    with D have " y < i" " i\<le>csucc(y)" and O: "Card(y)"
      using not_lt_imp_le lt_Ord Card_csucc Card_is_Ord
      by auto
    with assms have "csucc(y)\<le>i""i\<le>csucc(y)" using csucc_le by auto
    then have "i=csucc(y)" using le_anti_sym by auto
    with O have "\<exists>j. Card(j) \<and> i=csucc(j)" by auto
  } thus ?thesis by auto
qed

text\<open>Given an ordinal bounded by a cardinal in ordinal order, we can change
to the order of sets.\<close>

lemma le_imp_lesspoll:
  assumes "Card(Q)"
  shows "A \<le> Q \<Longrightarrow> A \<lesssim> Q"
proof -
  assume "A \<le> Q"
  then have "A<Q\<or>A=Q" using le_iff by auto
  then have "A\<approx>Q\<or>A< Q" using eqpoll_refl by auto
  with assms have "A\<approx>Q\<or>A\<prec> Q" using lt_Card_imp_lesspoll by auto
  then show "A\<lesssim>Q" using lesspoll_def eqpoll_imp_lepoll by auto
qed

text\<open>There are two types of infinite cardinals, the natural numbers
and those that have at least one infinite strictly smaller cardinal.\<close>

lemma InfCard_cases_disj:
  assumes "InfCard(Q)"
  shows "Q=nat \<or> (\<exists>j. csucc(j)\<lesssim>Q \<and> InfCard(j))"
proof-
  {
    assume "\<forall>j. \<not> csucc(j) \<lesssim> Q \<or> \<not> InfCard(j)"
    then have D: "\<not> csucc(nat) \<lesssim> Q" using InfCard_nat by auto
    with D assms have "\<not>(csucc(nat) \<le> Q)" using le_imp_lesspoll InfCard_is_Card 
      by auto
    with assms have "Q<(csucc(nat))" 
      using not_le_iff_lt Card_is_Ord Card_csucc Card_is_Ord
        Card_is_Ord InfCard_is_Card Card_nat by auto  
    with assms have "Q\<le>nat" using Card_lt_csucc_iff InfCard_is_Card Card_nat 
      by auto
    with assms have "Q=nat" using InfCard_def le_anti_sym by auto
  }
  thus ?thesis by auto
qed

text\<open>A more readable version of standard Isabelle/ZF \<open>Ord_linear_lt\<close>\<close>

lemma Ord_linear_lt_IML: assumes "Ord(i)" "Ord(j)"
  shows "i<j \<or> i=j \<or> j<i"
  using assms lt_def Ord_linear disjE by simp 

text\<open>A set is injective and not bijective to the successor of a cardinal
if and only if it is injective and possibly bijective to the cardinal.\<close>

lemma Card_less_csucc_eq_le: 
  assumes "Card(m)"
  shows "A \<prec> csucc(m) \<longleftrightarrow> A \<lesssim> m"
proof
  have S: "Ord(csucc(m))" using Card_csucc Card_is_Ord assms by auto
  {
    assume A: "A \<prec> csucc(m)"
    with S have "|A|\<approx>A" using lesspoll_imp_eqpoll by auto
    also from A have "\<dots>\<prec> csucc(m)" by auto
    finally have "|A|\<prec> csucc(m)" by auto
    then have "|A|\<lesssim>csucc(m)""~(|A|\<approx>csucc(m))" using lesspoll_def by auto
    with S have "||A||\<le>csucc(m)""|A|\<noteq>csucc(m)" using lepoll_cardinal_le by auto
    then have "|A|\<le>csucc(m)" "|A|\<noteq>csucc(m)" using Card_def Card_cardinal by auto
    then have I: "~(csucc(m)<|A|)" "|A|\<noteq>csucc(m)" using le_imp_not_lt by auto
    from S have "csucc(m)<|A| \<or> |A|=csucc(m) \<or> |A|<csucc(m)"
      using Card_cardinal Card_is_Ord Ord_linear_lt_IML by auto 
    with I have "|A|<csucc(m)" by simp     
    with assms have "|A|\<le>m" using Card_lt_csucc_iff Card_cardinal
      by auto
    then have "|A|=m\<or> |A|< m" using le_iff by auto
    then have "|A|\<approx>m\<or>|A|< m" using eqpoll_refl by auto
    then have "|A|\<approx>m\<or>|A|\<prec> m" using lt_Card_imp_lesspoll assms by auto
    then have T:"|A|\<lesssim>m" using lesspoll_def eqpoll_imp_lepoll by auto
    from A S have "A\<approx>|A|" using lesspoll_imp_eqpoll eqpoll_sym by auto
    also from T have "\<dots>\<lesssim>m" by auto
    finally show "A\<lesssim>m" by simp
  }
  {
    assume A: "A\<lesssim>m"
    from assms have "m\<prec>csucc(m)" using lt_Card_imp_lesspoll Card_csucc Card_is_Ord
      lt_csucc by auto
    with A show "A\<prec>csucc(m)" using lesspoll_trans1 by auto
  }
qed

text\<open>If the successor of a cardinal is infinite, so is the original
cardinal.\<close>

lemma csucc_inf_imp_inf:
  assumes "Card(j)" and "InfCard(csucc(j))"
  shows "InfCard(j)"
proof-
  {
    assume f:"Finite (j)"
    then obtain n where "n\<in>nat" "j\<approx>n" using Finite_def by auto
    with assms(1) have TT: "j=n" "n\<in>nat" 
      using cardinal_cong nat_into_Card Card_def by auto
    then have Q:"succ(j)\<in>nat" using nat_succI by auto
    with f TT have T: "Finite(succ(j))" "Card(succ(j))" 
      using nat_into_Card nat_succI by auto 
    from T(2) have "Card(succ(j))\<and> j<succ(j)" using Card_is_Ord by auto
    moreover from this have "Ord(succ(j))" using Card_is_Ord by auto
    moreover
    { fix x
      assume A: "x<succ(j)"
      {
        assume "Card(x)\<and> j<x"
        with A have "False" using lt_trans1 by auto
      }
      hence "~(Card(x)\<and> j<x)" by auto
    } 
    ultimately have "(\<mu> L. Card(L) \<and> j < L)=succ(j)"
      by (rule Least_equality)
    then have "csucc(j)=succ(j)" using csucc_def by auto
    with Q have "csucc(j)\<in>nat" by auto
    then have "csucc(j)<nat" using lt_def Card_nat Card_is_Ord by auto
    with assms(2) have "False" using InfCard_def lt_trans2 by auto
  }
  then have "~(Finite (j))" by auto
  with assms(1) show ?thesis using Inf_Card_is_InfCard by auto
qed

text\<open>Since all the cardinals previous to \<open>nat\<close>
are finite, it cannot be a successor cardinal; hence it is 
a \<open>LimitC\<close> cardinal.\<close>

corollary LimitC_nat:
  shows "LimitC(nat)"
proof-
  note Card_nat
  moreover have "0<nat" using lt_def by auto
  moreover
  {
    fix y
    assume AS: "y<nat""Card(y)"
    then have ord: "Ord(y)" unfolding lt_def by auto
    then have Cacsucc: "Card(csucc(y))" using Card_csucc by auto
    {
      assume "nat\<le>csucc(y)"
      with Cacsucc have "InfCard(csucc(y))" using InfCard_def by auto
      with AS(2) have "InfCard(y)" using csucc_inf_imp_inf by auto
      then have "nat\<le>y" using InfCard_def by auto
      with AS(1) have "False" using lt_trans2 by auto
    }
    hence "~(nat\<le>csucc(y))" by auto
    then have "csucc(y)<nat" using not_le_iff_lt Ord_nat Cacsucc Card_is_Ord by auto
  }
  ultimately show ?thesis using LimitC_def by auto
qed

subsection\<open>Main result on cardinals (without the Axiom of Choice)\<close>

text\<open>If two sets are strictly injective to an infinite cardinal,
then so is its union. For the case of successor cardinal, this
theorem is done in the isabelle library in a more general setting;
 but that theorem is of not
use in the case where \<open>LimitC(Q)\<close> and it also makes use
of the Axiom of Choice. The mentioned theorem is in the
theory file \<open>Cardinal_AC.thy\<close>\<close>

text\<open>Note that if $Q$ is finite and different from $1$, let's assume $Q=n$,
then the union of $A$ and $B$ is not bounded by $Q$.
Counterexample: two disjoint sets of $n-1$ elements each
have a union of $2n-2$ elements which are more than $n$.

Note also that if $Q=1$ then $A$ and $B$ must be empty
and the union is then empty too; and $Q$ cannot be \<open>0\<close> because
no set is injective and not bijective to \<open>0\<close>.

The proof is divided in two parts, first the case when
both sets $A$ and $B$ are finite; and second,
the part when at least one of them is infinite.
In the first part, it is used the fact that a finite
union of finite sets is finite. In the second part it
is used the linear order on cardinals (ordinals).
This proof can not be generalized to a setting with 
an infinite union easily.\<close>

lemma less_less_imp_un_less:
  assumes "A\<prec>Q" and "B\<prec>Q" and "InfCard(Q)"
  shows "A \<union> B\<prec>Q"
proof-
{
  assume "Finite (A) \<and> Finite(B)"
  then have "Finite(A \<union> B)" using Finite_Un by auto
  then obtain n where R: "A \<union> B \<approx>n"  "n\<in>nat" using Finite_def
    by auto
  then have "|A \<union> B|<nat" using lt_def  cardinal_cong
    nat_into_Card  Card_def  Card_nat Card_is_Ord by auto
  with assms(3) have T: "|A \<union> B|<Q" using InfCard_def lt_trans2 by auto
  from R have "Ord(n)""A \<union> B \<lesssim> n" using nat_into_Card Card_is_Ord eqpoll_imp_lepoll by auto
  then have "A \<union> B\<approx>|A \<union> B|" using lepoll_Ord_imp_eqpoll eqpoll_sym by auto
  also from T assms(3) have "\<dots>\<prec>Q" using lt_Card_imp_lesspoll InfCard_is_Card
    by auto
  finally have "A \<union> B\<prec>Q" by simp
}
moreover
{
  assume "~(Finite (A) \<and> Finite(B))"
  hence A: "~Finite (A) \<or> ~Finite(B)" by auto
  from assms have B: "|A|\<approx>A" "|B|\<approx>B" using lesspoll_imp_eqpoll lesspoll_imp_eqpoll
    InfCard_is_Card Card_is_Ord by auto
  from B(1) have Aeq: "\<forall>x. (|A|\<approx>x) \<longrightarrow> (A\<approx>x)"
    using eqpoll_sym eqpoll_trans by blast
  from B(2) have Beq: "\<forall>x. (|B|\<approx>x) \<longrightarrow> (B\<approx>x)"
    using eqpoll_sym eqpoll_trans by blast
  with A Aeq have "~Finite(|A|)\<or> ~Finite(|B|)" using Finite_def
    by auto
  then have D: "InfCard(|A|)\<or>InfCard(|B|)" 
    using Inf_Card_is_InfCard Inf_Card_is_InfCard  Card_cardinal by blast
  {
    assume AS: "|A| < |B|"
    {
      assume "~InfCard(|A|)"
      with D have "InfCard(|B|)" by auto
    }
    moreover
    {
      assume "InfCard(|A|)"
      then have "nat\<le>|A|" using InfCard_def by auto
      with AS have "nat<|B|" using lt_trans1 by auto
      then have "nat\<le>|B|" using leI by auto
      then have "InfCard(|B|)" using InfCard_def Card_cardinal by auto
    }
    ultimately have INFB: "InfCard(|B|)" by auto
    then have "2<|B|" using nat_less_infty by simp 
    then have AG: "2\<lesssim>|B|" using lt_Card_imp_lesspoll Card_cardinal lesspoll_def
      by auto
    from B(2) have "|B|\<approx>B" by simp 
    also from assms(2) have "\<dots>\<prec>Q" by auto
    finally have TTT: "|B|\<prec>Q" by simp 
    from B(1) have "Card(|B|)" "A \<lesssim>|A|" using eqpoll_sym Card_cardinal eqpoll_imp_lepoll 
      by auto
    with AS have "A\<prec>|B|" using  lt_Card_imp_lesspoll lesspoll_trans1 by auto
    then have I1: "A\<lesssim>|B|" using lesspoll_def by auto
    from B(2) have I2: "B\<lesssim>|B|" using  eqpoll_sym eqpoll_imp_lepoll by auto
    have "A \<union> B\<lesssim>A+B" using Un_lepoll_sum by auto
    also from I1 I2 have "\<dots>\<lesssim> |B| + |B|" using sum_lepoll_mono by auto
    also from AG have "\<dots>\<lesssim>|B| * |B|" using sum_lepoll_prod by auto
    also from assms(3) INFB have "\<dots>\<approx>|B|" using InfCard_square_eqpoll
      by auto
    finally have "A \<union> B\<lesssim>|B|" by simp
    also from TTT have "\<dots>\<prec>Q" by auto
    finally have "A \<union> B\<prec>Q" by simp 
  }
  moreover
  {
    assume AS: "|B| < |A|"
    {
      assume "~InfCard(|B|)"
      with D have "InfCard(|A|)" by auto
    }
    moreover
    {
      assume "InfCard(|B|)"
      then have "nat\<le>|B|" using InfCard_def by auto
      with AS have "nat<|A|" using lt_trans1 by auto
      then have "nat\<le>|A|" using leI by auto
      then have "InfCard(|A|)" using InfCard_def Card_cardinal by auto
    }
    ultimately have INFB: "InfCard(|A|)" by auto
    then have "2<|A|" using nat_less_infty by simp
    then have AG: "2\<lesssim>|A|" using lt_Card_imp_lesspoll Card_cardinal lesspoll_def
        by auto
    from B(1) have "|A|\<approx>A" by simp
    also from assms(1) have "\<dots>\<prec>Q" by auto
    finally have TTT: "|A|\<prec>Q" by simp
    from B(2) have "Card(|A|)" "B \<lesssim>|B|" using eqpoll_sym Card_cardinal eqpoll_imp_lepoll 
      by auto
    with AS have "B\<prec>|A|" using  lt_Card_imp_lesspoll lesspoll_trans1 by auto
    then have I1: "B\<lesssim>|A|" using lesspoll_def by auto
    from B(1) have I2: "A\<lesssim>|A|" using eqpoll_sym eqpoll_imp_lepoll by auto
    have "A \<union> B\<lesssim>A+B" using Un_lepoll_sum by auto
    also from I1 I2 have "\<dots>\<lesssim> |A| + |A|" using sum_lepoll_mono by auto
    also from AG have "\<dots>\<lesssim>|A| * |A|" using sum_lepoll_prod by auto
    also from INFB assms(3) have "\<dots>\<approx>|A|" using InfCard_square_eqpoll
       by auto
    finally have "A \<union> B\<lesssim>|A|" by simp
    also from TTT have "\<dots>\<prec>Q" by auto
    finally have "A \<union> B\<prec>Q" by simp 
    }
    moreover
    {
      assume AS: "|A|=|B|"
      with D have INFB: "InfCard(|A|)" by auto
      then have "2<|A|" using nat_less_infty by simp
      then have AG: "2\<lesssim>|A|" using lt_Card_imp_lesspoll Card_cardinal using lesspoll_def
        by auto
      from B(1) have "|A|\<approx>A" by simp 
      also from assms(1) have "\<dots>\<prec>Q" by auto
      finally have TTT: "|A|\<prec>Q" by simp
      from AS B have I1: "A\<lesssim>|A|"and I2:"B\<lesssim>|A|" using eqpoll_refl eqpoll_imp_lepoll
        eqpoll_sym by auto
      have "A \<union> B\<lesssim>A+B" using Un_lepoll_sum by auto
      also from I1 I2 have "\<dots>\<lesssim> |A| + |A|" using sum_lepoll_mono by auto
      also from AG have "\<dots>\<lesssim>|A| * |A|" using sum_lepoll_prod  by auto
      also from assms(3) INFB have "\<dots>\<approx>|A|" using InfCard_square_eqpoll
        by auto
      finally have "A \<union> B\<lesssim>|A|" by simp 
      also from TTT have "\<dots>\<prec>Q" by auto
      finally have "A \<union> B\<prec>Q" by simp
    }
    ultimately have "A \<union> B\<prec>Q" using Ord_linear_lt_IML Card_cardinal Card_is_Ord by auto
  }
  ultimately show "A \<union> B\<prec>Q" by auto
qed

subsection\<open>Choice axioms\<close>

text\<open>We want to prove some theorems assuming that some version of the Axiom of Choice holds.
  To avoid introducing it as an axiom we will define an appropriate predicate and put that in the 
  assumptions of the theorems. That way technically we stay inside ZF.\<close>

text\<open>The first predicate we define states that the axiom of $Q$-choice holds for subsets of $K$ if 
  we can find a choice function for every family of subsets of $K$ whose (that family's) 
  cardinality does not exceed $Q$.\<close>

definition
  AxiomCardinalChoice ("{the axiom of}_{choice holds for subsets}_") where
  "{the axiom of} Q {choice holds for subsets}K \<equiv> Card(Q) \<and> (\<forall> M N. (M \<lesssim>Q \<and>  (\<forall>t\<in>M. N`t\<noteq>0 \<and> N`t\<subseteq>K)) \<longrightarrow> (\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t)))"

text\<open>Next we define a general form of $Q$ choice where we don't require a collection of sets
  to be included in a set.\<close>

definition
  AxiomCardinalChoiceGen ("{the axiom of}_{choice holds}") where
  "{the axiom of} Q {choice holds} \<equiv> Card(Q) \<and> (\<forall> M N. (M \<lesssim>Q \<and>  (\<forall>t\<in>M. N`t\<noteq>0)) \<longrightarrow> (\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t)))"


text\<open>The axiom of choice holds if and only if the \<open>AxiomCardinalChoice\<close>
  holds for every couple of a cardinal \<open>Q\<close> and a set \<open>K\<close>.\<close>

lemma choice_subset_imp_choice:
  shows "{the axiom of} Q {choice holds} \<longleftrightarrow> (\<forall> K. {the axiom of} Q {choice holds for subsets}K)"
  unfolding AxiomCardinalChoice_def AxiomCardinalChoiceGen_def by blast

text\<open>A choice axiom for greater cardinality implies one for 
smaller cardinality\<close>

lemma greater_choice_imp_smaller_choice:
  assumes "Q\<lesssim>Q1" "Card(Q)"
  shows "{the axiom of} Q1 {choice holds} \<longrightarrow> ({the axiom of} Q {choice holds})" using assms
  AxiomCardinalChoiceGen_def lepoll_trans by auto   

text\<open>If we have a surjective function from a set which is injective to a set 
  of ordinals, then we can find an injection which goes the other way.\<close>

lemma surj_fun_inv:
  assumes "f \<in> surj(A,B)" "A\<subseteq>Q" "Ord(Q)"
  shows "B\<lesssim>A"
proof-
  let ?g = "{\<langle>m,\<mu> j. j\<in>A \<and> f`(j)=m\<rangle>. m\<in>B}" 
  have "?g:B\<rightarrow>range(?g)" using lam_is_fun_range by simp
  then have fun: "?g:B\<rightarrow>?g``(B)" using range_image_domain by simp
  from assms(2,3) have OA: "\<forall>j\<in>A. Ord(j)" using lt_def Ord_in_Ord by auto
  {
    fix x
    assume "x\<in>?g``(B)"
    then have "x\<in>range(?g)" and "\<exists>y\<in>B. \<langle>y,x\<rangle>\<in>?g" by auto
    then obtain y where T: "x=(\<mu> j. j\<in>A\<and> f`(j)=y)" and "y\<in>B" by auto
    with assms(1) OA obtain z where P: "z\<in>A \<and> f`(z)=y" "Ord(z)" unfolding surj_def 
      by auto
    with T have "x\<in>A \<and> f`(x)=y" using LeastI by simp  
    hence "x\<in>A" by simp
  }
  then have "?g``(B) \<subseteq> A" by auto
  with fun have fun2: "?g:B\<rightarrow>A" using fun_weaken_type by auto
  then have "?g\<in>inj(B,A)" 
  proof -
    {
      fix w x
      assume AS: "?g`w=?g`x" "w\<in>B" "x\<in>B"
      from assms(1) OA AS(2,3) obtain wz xz where 
        P1: "wz\<in>A \<and> f`(wz)=w"  "Ord(wz)" and P2: "xz\<in>A \<and> f`(xz)=x"  "Ord(xz)" 
        unfolding surj_def by blast
      from P1 have "(\<mu> j. j\<in>A\<and> f`j=w) \<in> A \<and> f`(\<mu> j. j\<in>A\<and> f`j=w)=w" 
        by (rule LeastI)
      moreover from P2 have "(\<mu> j. j\<in>A\<and> f`j=x) \<in> A \<and> f`(\<mu> j. j\<in>A\<and> f`j=x)=x"
        by (rule LeastI) 
      ultimately have R: "f`(\<mu> j. j\<in>A\<and> f`j=w)=w" "f`(\<mu> j. j\<in>A\<and> f`j=x)=x" 
        by auto
      from AS have "(\<mu> j. j\<in>A\<and> f`(j)=w)=(\<mu> j. j\<in>A \<and> f`(j)=x)" 
        using apply_equality fun2 by auto
      hence "f`(\<mu> j. j\<in>A \<and> f`(j)=w) = f`(\<mu> j. j\<in>A \<and> f`(j)=x)" by auto
      with R(1) have "w = f`(\<mu> j. j\<in>A\<and> f`j=x)" by auto
      with R(2) have "w=x" by auto
    }
    hence "\<forall>w\<in>B. \<forall>x\<in>B. ?g`(w) = ?g`(x) \<longrightarrow> w = x" 
      by auto 
    with fun2 show "?g\<in>inj(B,A)" unfolding inj_def by auto     
  qed
  then show ?thesis unfolding lepoll_def by auto
qed

text\<open>The difference with the previous result is that in this one
\<open>A\<close> is not a subset of an ordinal, it is only injective
with one.\<close>

theorem surj_fun_inv_2:
  assumes "f:surj(A,B)" "A\<lesssim>Q" "Ord(Q)"
  shows "B\<lesssim>A"
proof-
  from assms(2) obtain h where h_def: "h\<in>inj(A,Q)" using lepoll_def by auto
  then have bij: "h\<in>bij(A,range(h))" using inj_bij_range by auto
  then obtain h1 where "h1\<in>bij(range(h),A)" using bij_converse_bij by auto
  then have "h1 \<in> surj(range(h),A)" using bij_def by auto
  with assms(1) have "(f O h1)\<in>surj(range(h),B)" using comp_surj by auto
  moreover
  {
    fix x
    assume p: "x\<in>range(h)"
    from bij have "h\<in>surj(A,range(h))" using bij_def by auto
    with p obtain q where "q\<in>A" and "h`(q)=x" using surj_def by auto
    then have "x\<in>Q" using h_def inj_def by auto
  }
  then have "range(h)\<subseteq>Q" by auto
  ultimately have "B\<lesssim>range(h)" using surj_fun_inv assms(3) by auto
  moreover have "range(h)\<approx>A" using bij eqpoll_def eqpoll_sym by blast
  ultimately show "B\<lesssim>A" using lepoll_eq_trans by auto
qed

subsection\<open>Finite choice\<close>

text\<open>In ZF every finite collection of non-empty sets has a choice function, i.e. a function that
  selects one element from each set of the collection. In this section we prove various forms of 
  that claim.\<close>

text\<open>The axiom of finite choice always holds.\<close>

theorem finite_choice:
  assumes "n\<in>nat"
  shows "{the axiom of} n {choice holds}"
proof -
  note assms(1)
  moreover
  {
    fix M N assume "M\<lesssim>0" "\<forall>t\<in>M. N`t\<noteq>0"
    then have "M=0" using lepoll_0_is_0 by auto
    then have "{\<langle>t,0\<rangle>. t\<in>M}:Pi(M,\<lambda>t. N`t)" unfolding Pi_def domain_def function_def Sigma_def by auto
    moreover from \<open>M=0\<close> have "\<forall>t\<in>M. {\<langle>t,0\<rangle>. t\<in>M}`t\<in>N`t" by auto
    ultimately have "(\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t))" by auto
  }
  then have "(\<forall> M N. (M \<lesssim>0 \<and>  (\<forall>t\<in>M. N`t\<noteq>0)) \<longrightarrow> (\<exists>f. f:Pi(M,\<lambda>t. N`t) \<and> (\<forall>t\<in>M. f`t\<in>N`t)))" 
    by auto
  then have "{the axiom of} 0 {choice holds}" using AxiomCardinalChoiceGen_def nat_into_Card 
    by auto
  moreover { 
    fix x
    assume as: "x\<in>nat" "{the axiom of} x {choice holds}"
    {
      fix M N assume ass: "M\<lesssim>succ(x)" "\<forall>t\<in>M. N`t\<noteq>0"
      {
        assume "M\<lesssim>x"
        from as(2) ass(2) have 
          "(M \<lesssim> x \<and> (\<forall>t\<in>M. N ` t \<noteq> 0)) \<longrightarrow> (\<exists>f. f \<in> Pi(M,\<lambda>t. N ` t) \<and> (\<forall>t\<in>M. f ` t \<in> N ` t))" 
            unfolding AxiomCardinalChoiceGen_def by auto
        with \<open>M\<lesssim>x\<close> ass(2) have "(\<exists>f. f \<in> Pi(M,\<lambda>t. N ` t) \<and> (\<forall>t\<in>M. f ` t \<in> N ` t))" 
          by auto
      }
      moreover
      {
        assume "M\<approx>succ(x)"
        then obtain f where f:"f\<in>bij(succ(x),M)" using eqpoll_sym eqpoll_def by blast 
        moreover
        have "x\<in>succ(x)" unfolding succ_def by auto
        ultimately have "restrict(f,succ(x)-{x})\<in>bij(succ(x)-{x},M-{f`x})" using bij_restrict_rem 
          by auto 
        moreover
        have "x\<notin>x" using mem_not_refl by auto
        then have "succ(x)-{x}=x" unfolding succ_def by auto
        ultimately have "restrict(f,x)\<in>bij(x,M-{f`x})" by auto
        then have "x\<approx>M-{f`x}" unfolding eqpoll_def by auto
        then have "M-{f`x}\<approx>x" using eqpoll_sym by auto
        then have "M-{f`x}\<lesssim>x" using eqpoll_imp_lepoll by auto
        with as(2) ass(2) have "(\<exists>g. g \<in> Pi(M-{f`x},\<lambda>t. N ` t) \<and> (\<forall>t\<in>M-{f`x}. g ` t \<in> N ` t))" 
          unfolding AxiomCardinalChoiceGen_def by auto
        then obtain g where g: "g\<in> Pi(M-{f`x},\<lambda>t. N ` t)" "\<forall>t\<in>M-{f`x}. g ` t \<in> N ` t" 
          by auto
        from f have ff: "f`x\<in>M" using bij_def inj_def apply_funtype by auto
        with ass(2) have "N`(f`x)\<noteq>0" by auto
        then obtain y where y: "y\<in>N`(f`x)" by auto
        from g(1) have gg: "g\<subseteq>Sigma(M-{f`x},(`)(N))" unfolding Pi_def by auto
        with y ff have "g \<union>{\<langle>f`x, y\<rangle>}\<subseteq>Sigma(M, (`)(N))" unfolding Sigma_def by auto 
        moreover
        from g(1) have dom: "M-{f`x}\<subseteq>domain(g)" unfolding Pi_def by auto
        then have "M\<subseteq>domain(g \<union>{\<langle>f`x, y\<rangle>})" unfolding domain_def by auto 
        moreover
        from gg g(1) have noe: "~(\<exists>t. \<langle>f`x,t\<rangle>\<in>g)" and "function(g)"
          unfolding domain_def Pi_def Sigma_def by auto  
        with dom have fg: "function(g \<union>{\<langle>f`x, y\<rangle>})" unfolding function_def by blast 
        ultimately have PP: "g \<union>{\<langle>f`x, y\<rangle>}\<in>Pi(M,\<lambda>t. N ` t)" unfolding Pi_def by auto
        have "\<langle>f`x, y\<rangle> \<in> g \<union>{\<langle>f`x, y\<rangle>}" by auto
        from this fg have "(g \<union>{\<langle>f`x, y\<rangle>})`(f`x)=y" by (rule function_apply_equality)
        with y have "(g \<union>{\<langle>f`x, y\<rangle>})`(f`x)\<in>N`(f`x)" by auto 
        moreover
        {
          fix t assume A:"t\<in>M-{f`x}"
          with g(1) have "\<langle>t,g`t\<rangle>\<in>g" using apply_Pair by auto
          then have "\<langle>t,g`t\<rangle>\<in>(g \<union>{\<langle>f`x, y\<rangle>})" by auto
          then have "(g \<union>{\<langle>f`x, y\<rangle>})`t=g`t" using apply_equality PP by auto
          with A have "(g \<union>{\<langle>f`x, y\<rangle>})`t\<in>N`t" using g(2) by auto
        }
        ultimately have "\<forall>t\<in>M. (g \<union>{\<langle>f`x, y\<rangle>})`t\<in>N`t" by auto
        with PP have "\<exists>g. g\<in>Pi(M,\<lambda>t. N ` t) \<and> (\<forall>t\<in>M. g`t\<in>N`t)" by auto
      }
    ultimately have "\<exists>g. g \<in> Pi(M, \<lambda>t. N`t) \<and> (\<forall>t\<in>M. g ` t \<in> N ` t)" using as(1) ass(1)
      lepoll_succ_disj by auto
    }
    then have "\<forall>M N. M \<lesssim> succ(x)\<and>(\<forall>t\<in>M. N`t\<noteq>0)\<longrightarrow>(\<exists>g. g \<in> Pi(M,\<lambda>t. N ` t) \<and> (\<forall>t\<in>M. g ` t \<in> N ` t))" 
      by auto
    then have "{the axiom of}succ(x){choice holds}" 
      using AxiomCardinalChoiceGen_def nat_into_Card as(1) nat_succI by auto
  }
  ultimately show ?thesis by (rule nat_induct)
qed

text\<open>The choice functions of a collection $\mathcal{A}$ are functions $f$ defined on 
  $\mathcal{A}$ and valued in $\bigcup \mathcal{A}$ such that $f(A)\in A$ 
  for every $A\in \mathcal{A}$.\<close>

definition
  "ChoiceFunctions(\<A>) \<equiv> {f\<in>\<A>\<rightarrow>\<Union>\<A>. \<forall>A\<in>\<A>. f`(A)\<in>A}"

text\<open>For finite collections of non-empty sets the set of choice functions is non-empty.\<close>

theorem finite_choice1: assumes "Finite(\<A>)" and "\<forall>A\<in>\<A>. A\<noteq>\<emptyset>"
  shows "ChoiceFunctions(\<A>) \<noteq> \<emptyset>"
proof -
  let ?N = "id(\<A>)"
  let ?\<N> = "(\<lambda>t. ?N`(t))"
  from assms(1) obtain n where "n\<in>nat" and "\<A>\<approx>n"
    unfolding Finite_def by auto  
  from assms(2) \<open>\<A>\<approx>n\<close> have "\<A>\<lesssim>n" and "\<forall>A\<in>\<A>. ?N`(A)\<noteq>\<emptyset>" 
    using eqpoll_imp_lepoll by simp_all
  with \<open>n\<in>nat\<close> obtain f where "f\<in>Pi(\<A>,?\<N>)"
    using finite_choice unfolding AxiomCardinalChoiceGen_def by blast
  have "Pi(\<A>,?\<N>) = {f\<in>\<A>\<rightarrow>(\<Union>A\<in>\<A>. ?\<N>(A)). \<forall>A\<in>\<A>. f`(A)\<in>?\<N>(A)}"
    by (rule pi_fun_space)
  with \<open>f\<in>Pi(\<A>,?\<N>)\<close> show ?thesis
    unfolding ChoiceFunctions_def by auto
qed

text\<open>If a set $X$ is finite and such that for every $x\in X$ we can find
  $y\in $ such that the property $P(x,y)$ holds, then there there is a 
  function $f:X\rightarrow Y$ such that $P(x,f(x))$ holds for every $x\in X$. \<close>

lemma finite_choice_fun: assumes "Finite(X)" "\<forall>x\<in>X. \<exists>y\<in>Y. P(x,y)"
  shows "\<exists>f\<in>X\<rightarrow>Y. \<forall>x\<in>X. P(x,f`(x))"
proof -
  let ?N = "{\<langle>x,{y\<in>Y. P(x,y)}\<rangle>. x\<in>X}"
  let ?\<N> = "(\<lambda>t. ?N`(t))"
  from assms(1) obtain n where "n\<in>nat" and "X\<approx>n"
    unfolding Finite_def by auto
  have I: "\<forall>x\<in>X. ?N`(x) = {y\<in>Y. P(x,y)}" using ZF_fun_from_tot_val2 by simp
  with assms(2) \<open>X\<approx>n\<close> have "X\<lesssim>n" and "\<forall>x\<in>X. ?N`(x)\<noteq>\<emptyset>" 
    using eqpoll_imp_lepoll by auto
  with \<open>n\<in>nat\<close> obtain f where "f\<in>Pi(X,?\<N>)" and II: "\<forall>x\<in>X. f`(x)\<in>?N`(x)"
    using finite_choice unfolding AxiomCardinalChoiceGen_def by blast
  have "Pi(X,?\<N>) = {f\<in>X\<rightarrow>(\<Union>x\<in>X. ?\<N>(x)). \<forall>x\<in>X. f`(x)\<in>?\<N>(x)}"
    by (rule pi_fun_space)
  with \<open>f\<in>Pi(X,?\<N>)\<close> I II show ?thesis using func1_1_L1A by auto
qed

subsection\<open>Pigeonhole principle\<close>

text\<open>In this section we present various versions of the pigeonhole principle. 
  Simplifying somewhat the pigeonhole principle states that if you have more items than containers, 
  at least one container must hold more than one item. This obvious observation is a surprisingly 
  effective proof technique.\<close>

text\<open>If a function maps a set with larger cardinality to a set with smaller cardinality
  then we can find two different elements of the domain that map to the same value.\<close>

lemma pigeonhole: assumes "f:X\<rightarrow>Y" "Y\<prec>X"
  shows "\<exists>x\<^sub>1\<in>X. \<exists>x\<^sub>2\<in>X. x\<^sub>1\<noteq>x\<^sub>2 \<and> f`(x\<^sub>1)=f`(x\<^sub>2)"
proof -
  { assume "\<forall>x\<^sub>1\<in>X. \<forall>x\<^sub>2\<in>X. f`(x\<^sub>1)=f`(x\<^sub>2) \<longrightarrow> x\<^sub>1=x\<^sub>2"
    with assms have False using eqpollI 
      unfolding inj_def lepoll_def lesspoll_def by blast
  } thus ?thesis by auto
qed

text\<open>In a list that is longer than its codomain we can find indices $i < j$ where the 
  the list elements repeat.\<close>

lemma pigeonhole_list: assumes "n\<in>nat" "X\<prec>n" "b:n\<rightarrow>X"
  shows "\<exists>i\<in>n. \<exists>j\<in>n. i < j \<and> b`(i) = b`(j)"
proof -
  from assms(2,3) obtain i j where "i\<in>n" "j\<in>n" "i\<noteq>j" "b`(i) = b`(j)"
    using pigeonhole by blast
  from assms(1) \<open>i\<in>n\<close> \<open>j\<in>n\<close> \<open>i\<noteq>j\<close> have "i < j \<or> j < i"
    using elem_nat_is_nat(2) nat_mem_total by simp
  with \<open>i\<in>n\<close> \<open>j\<in>n\<close> \<open>b`(i) = b`(j)\<close> show ?thesis by force
qed

subsection\<open>Countability vs enumerability\<close>

text\<open>There are different definitions of the notion of countability floating around.
  In the presence if the Axiom of Choice they are typically equivalent, but without
  AC they are often not. In this section we define the notions to have a reference 
  what exactly we mean by saying that "$X$ is enumerable" or "$X$ is countable. \<close>

text\<open>We say that a set $X$ is enumerable if it is empty or there is a surjection from the set of
  natural numbers onto $X$. We (somewhat arbitrarily) want the empty set to be enumerable, 
  but there are no functions whose domain is the set of natural numbers (or any nonempty set) 
  and whose codomain is empty, so there are no surjections from natural numbers to $\emptyset$.
  Hence we have to add the empty set as a special case.\<close>

definition IsEnumerable ("_ {is enumerable}" [90] 91) where
  "X {is enumerable} \<equiv> X=\<emptyset> \<or> surj(nat,X)\<noteq>\<emptyset>"

text\<open>A set is enumerable iff there exist a sequence that includes all elements of $X$.\<close>

lemma enumerable_iff_seq: 
  shows "X {is enumerable} \<longleftrightarrow> (\<exists>Y. \<exists>s\<in>nat\<rightarrow>Y. X\<subseteq>s``(nat))"
proof
  assume "X {is enumerable}"
  then have "X=\<emptyset> \<or> surj(nat,X)\<noteq>\<emptyset>" unfolding IsEnumerable_def 
    by simp
  moreover have "X=\<emptyset> \<longrightarrow> (\<exists>Y. \<exists>s\<in>nat\<rightarrow>Y. X\<subseteq>s``(nat))"
    using func1_3_L1 by blast
  moreover have "surj(nat,X)\<noteq>\<emptyset> \<longrightarrow> (\<exists>Y. \<exists>s\<in>nat\<rightarrow>Y. X\<subseteq>s``(nat))"
    using func_imagedef unfolding surj_def by force
  ultimately show "\<exists>Y. \<exists>s\<in>nat\<rightarrow>Y. X\<subseteq>s``(nat)" by auto
next
  assume "\<exists>Y. \<exists>s\<in>nat\<rightarrow>Y. X\<subseteq>s``(nat)"
  then obtain Y s where "s\<in>nat\<rightarrow>Y" and "X\<subseteq>s``(nat)" by auto
  have "X=\<emptyset> \<longrightarrow> X {is enumerable}" unfolding IsEnumerable_def
    by simp
  moreover
  { assume "X\<noteq>\<emptyset>"
    then obtain x\<^sub>0 where "x\<^sub>0\<in>X" by auto
    let ?f = "{\<langle>n,if s`(n) \<in> X then s`(n) else x\<^sub>0\<rangle>. n\<in>nat}"
    from \<open>x\<^sub>0\<in>X\<close> have "?f:nat\<rightarrow>X" using ZF_fun_from_total
      by simp
    with \<open>X\<subseteq>s``(nat)\<close> \<open>s\<in>nat\<rightarrow>Y\<close> have "X {is enumerable}"
      using func_imagedef ZF_fun_from_tot_val1
      unfolding surj_def IsEnumerable_def by force
  }
  ultimately show "X {is enumerable}" by auto
qed

text\<open>A set $X$ is countable if there is an injection from $X$ to the natural numbers.\<close>

definition IsCountable ("_ {is countable}" [90] 91) where
  "X {is countable} \<equiv> inj(X,nat) \<noteq> \<emptyset>"

text\<open>If a set is countable then it is enumerable. In ZF the opposite implication cannot
  be proven.\<close>

lemma countable_enumerable: 
  assumes "X {is countable}" shows "X {is enumerable}"
proof -
  have "X=\<emptyset> \<longrightarrow> X {is enumerable}" unfolding IsEnumerable_def by simp
  moreover
  { assume "X\<noteq>\<emptyset>"
    then obtain x\<^sub>0 where "x\<^sub>0\<in>X" by auto
    from assms obtain f where "f\<in>inj(X,nat)"
      unfolding IsCountable_def by auto
    let ?g = "{\<langle>n,if n\<in>f``(X) then converse(f)`(n) else x\<^sub>0\<rangle>. n\<in>nat}"
    from \<open>f\<in>inj(X,nat)\<close> \<open>x\<^sub>0\<in>X\<close> have "?g:nat\<rightarrow>X" 
      using inj_inv_back_in_set ZF_fun_from_total by simp
    { fix x assume "x\<in>X"
      with \<open>f\<in>inj(X,nat)\<close> have "f`(x) \<in> nat" and "f`(x) \<in> f``(X)"
        using func_imagedef unfolding inj_def by auto
      with \<open>f\<in>inj(X,nat)\<close> \<open>x\<in>X\<close> have "\<exists>n\<in>nat. ?g`(n) = x"
        using left_inverse ZF_fun_from_tot_val1 by force
    }
    with \<open>?g:nat\<rightarrow>X\<close> have "surj(nat,X)\<noteq>\<emptyset>"
      unfolding surj_def by auto
  } then have "X\<noteq>\<emptyset> \<longrightarrow> X {is enumerable}" unfolding IsEnumerable_def
    by simp
  ultimately show "X {is enumerable}" by auto
qed

end 
