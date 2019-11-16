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

section \<open>Topology - examples\<close>

theory Topology_ZF_examples imports Topology_ZF Cardinal_ZF

begin

text\<open>
  This theory deals with some concrete examples of topologies.
\<close>

subsection\<open>CoCardinal Topology of a set $X$\<close>

text\<open>The collection of subsets of a set whose complement
is strictly bounded by a cardinal is a topology given some assumptions
on the cardinal.\<close>

definition Cocardinal ("CoCardinal _ _" 50) where
"CoCardinal X T \<equiv> {F\<in>Pow(X). X-F \<prec> T}\<union> {0}"

text\<open>For any set and any infinite cardinal; we prove that
\<open>CoCardinal X Q\<close> forms a topology. The proof is done
with an infinite cardinal, but it is obvious that the set \<open>Q\<close>
can be any set equipollent with an infinite cardinal.
It is a topology also if the set where the topology is defined is
too small or the cardinal too large; in this case, as it is later proved the topology
is a discrete topology. And the last case corresponds with \<open> "Q=1" \<close> which translates
in the indiscrete topology.\<close>

lemma CoCar_is_topology:
  assumes "InfCard (Q)"
  shows "(CoCardinal X Q) {is a topology}"
proof-
  let ?T="(CoCardinal X Q)"
  {
    fix M
    assume A:"M\<in>Pow(?T)"
    hence "M\<subseteq>?T" by auto
    then have "M\<subseteq>Pow(X)" using Cocardinal_def by auto
    then have "\<Union>M\<in>Pow(X)" by auto
    moreover
    {
      assume B:"M=0"
      then have "\<Union>M\<in>?T" using Cocardinal_def by auto
    }
    moreover
    {
      assume B:"M={0}"
      then have "\<Union>M\<in>?T" using Cocardinal_def by auto
    }
    moreover
    {
      assume B:"M \<noteq>0" "M\<noteq>{0}"
      from B obtain T where C:"T\<in>M" and "T\<noteq>0" by auto
      with A have D:"X-T \<prec> (Q)" using Cocardinal_def by auto
      from C have "X-\<Union>M\<subseteq>X-T" by blast
      with D have "X-\<Union>M\<prec> (Q)" using subset_imp_lepoll lesspoll_trans1 by blast
    }
    ultimately have "\<Union>M\<in>?T" using Cocardinal_def by auto
  }
  moreover
  {
    fix U and V
    assume "U\<in>?T" and "V\<in>?T"
    hence A:"U=0 \<or> (U\<in>Pow(X) \<and> X-U\<prec> (Q))" and
      B:"V=0 \<or> (V\<in>Pow(X) \<and> X-V\<prec> (Q))" using Cocardinal_def by auto
    hence D:"U\<in>Pow(X)""V\<in>Pow(X)" by auto
    have C:"X-(U \<inter> V)=(X-U)\<union>(X-V)" by fast
    with A B C have "U\<inter>V=0\<or>(U\<inter>V\<in>Pow(X) \<and> X-(U \<inter> V)\<prec> (Q))" using less_less_imp_un_less assms
      by auto
    hence "U\<inter>V\<in>?T" using Cocardinal_def by auto
  }
  ultimately show ?thesis using IsATopology_def by auto
qed

theorem topology0_CoCardinal:
  assumes "InfCard(T)"
  shows "topology0(CoCardinal X T)"
  using topology0_def CoCar_is_topology assms by auto

text\<open>It can also be proven that, if \<open>CoCardinal X T\<close> is a topology,
\<open> X\<noteq>0, Card(T)\<close> and \<open>T\<noteq>0\<close>; then \<open>T\<close> is an infinite cardinal, \<open> X\<prec>T\<close>
or \<open>T=1\<close>.
It follows from the fact that the union of two closed sets is closed.\<close>

text\<open>Choosing the appropriate cardinals, the cofinite and the cocountable topologies
are obtained.\<close>

text\<open>The cofinite topology is a very special topology because is extremely
related to the separation axiom $T_1$. It also appears naturally 
in algebraic geometry.\<close>

definition
  Cofinite ("CoFinite _" 90) where
  "CoFinite X \<equiv> CoCardinal X nat"

definition
  Cocountable ("CoCountable _" 90) where
  "CoCountable X \<equiv> CoCardinal X csucc(nat)"

subsection\<open>Total set, Closed sets, Interior, Closure and Boundary\<close>

text\<open>There are several assertions that can be done to the
 \<open>CoCardinal X T\<close> topology. In each case, we will not assume 
sufficient conditions for  \<open>CoCardinal X T\<close> to be a topology, but
they will be enough to do the calculations in every posible case.\<close>

text\<open>The topology is defined in the set $X$\<close>

lemma union_cocardinal:
  assumes "T\<noteq>0"
  shows "\<Union> (CoCardinal X T)=X"
proof-
  have X:"X-X=0" by auto
  have "0 \<lesssim> 0" by auto
  with assms have "0\<prec>1""1 \<lesssim>T" using not_0_is_lepoll_1 lepoll_imp_lesspoll_succ by auto
  then have "0\<prec>T" using lesspoll_trans2  by auto
  with X have "(X-X)\<prec>T" by auto
  then have "X\<in>(CoCardinal X T)" using Cocardinal_def by auto
  hence "X\<subseteq>\<Union> (CoCardinal X T)" by blast
  then show  "\<Union> (CoCardinal X T)=X" using Cocardinal_def by auto
qed

text\<open>The closed sets are the small subsets of $X$ and $X$ itself.\<close>

lemma closed_sets_cocardinal:
  assumes "T\<noteq>0"
  shows "D {is closed in} (CoCardinal X T) \<longleftrightarrow> (D\<in>Pow(X) & D\<prec>T)\<or> D=X"
proof-
  {
    assume A:"D \<subseteq> X" "X - D \<in> (CoCardinal X T) "" D \<noteq> X"
    from A(1,3) have "X-(X-D)=D" "X-D\<noteq>0" by (safe,blast+)
    with A(2) have "D\<prec>T" using Cocardinal_def by simp
  }
  with assms have "D {is closed in} (CoCardinal X T) \<longrightarrow> (D\<in>Pow(X) & D\<prec>T)\<or> D=X" using IsClosed_def
    union_cocardinal by auto
  moreover
  {
    assume A:"D \<prec> T""D \<subseteq> X"
    from A(2) have "X-(X-D)=D" by blast
    with A(1) have "X-(X-D)\<prec> T" by auto
    then have "X-D\<in> (CoCardinal X T)" using Cocardinal_def by auto
  }
  with assms have "(D\<in>Pow(X) & D\<prec>T)\<longrightarrow> D {is closed in} (CoCardinal X T)" using union_cocardinal
    IsClosed_def by auto
  moreover
  have "X-X=0" by auto
  then have "X-X\<in> (CoCardinal X T)"using Cocardinal_def by auto
  with assms have "X{is closed in} (CoCardinal X T)" using union_cocardinal
    IsClosed_def by auto
  ultimately show ?thesis by auto
qed

text\<open>The interior of a set is itself if it is open or \<open>0\<close> if
it isn't open.\<close>

lemma interior_set_cocardinal:
  assumes noC: "T\<noteq>0" and "A\<subseteq>X"
  shows "Interior(A,(CoCardinal X T))= (if ((X-A) \<prec> T) then A else 0)"
proof-
  from assms(2) have dif_dif:"X-(X-A)=A" by blast
  {
    assume "(X-A) \<prec> T"
    then have "(X-A)\<in>Pow(X) &(X-A) \<prec> T" by auto
    with noC have "(X-A) {is closed in} (CoCardinal X T)" using closed_sets_cocardinal
      by auto
    with noC have "X-(X-A)\<in>(CoCardinal X T)" using IsClosed_def union_cocardinal
      by auto
    with dif_dif have "A\<in>(CoCardinal X T)" by auto
    hence "A\<in>{U\<in>(CoCardinal X T). U \<subseteq> A}" by auto
    hence a1:"A\<subseteq>\<Union>{U\<in>(CoCardinal X T). U \<subseteq> A}" by auto
    have a2:"\<Union>{U\<in>(CoCardinal X T). U \<subseteq> A}\<subseteq>A" by blast
    from a1 a2 have "Interior(A,(CoCardinal X T))=A" using Interior_def by auto}
  moreover
  {
    assume as:"~((X-A) \<prec> T)"
    {
      fix U
      assume "U \<subseteq>A"
      hence "X-A \<subseteq> X-U" by blast
      then have Q:"X-A \<lesssim> X-U" using subset_imp_lepoll by auto
      {
        assume "X-U\<prec> T"
        with Q have "X-A\<prec> T" using lesspoll_trans1 by auto
        with as have "False"  by auto
      }
      hence "~((X-U) \<prec> T)" by auto
      then have "U\<notin>(CoCardinal X T)\<or>U=0" using Cocardinal_def by auto
    }
    hence "{U\<in>(CoCardinal X T). U \<subseteq> A}\<subseteq>{0}"  by blast
    then have "Interior(A,(CoCardinal X T))=0" using Interior_def by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>$X$ is a closed set that contains $A$.
This lemma is necessary because we cannot
use the lemmas proven in the \<open>topology0\<close> context since
\<open> T\<noteq>0"} is too weak for
 \<open>CoCardinal X T\<close> to be a topology.\<close>

lemma X_closedcov_cocardinal:
  assumes "T\<noteq>0""A\<subseteq>X"
  shows "X\<in>ClosedCovers(A,(CoCardinal X T))" using ClosedCovers_def
  using union_cocardinal closed_sets_cocardinal assms by auto

text\<open>The closure of a set is itself if it is closed or \<open>X\<close> if
it isn't closed.\<close>

lemma closure_set_cocardinal:
  assumes "T\<noteq>0""A\<subseteq>X"
  shows "Closure(A,(CoCardinal X T))=(if (A \<prec> T) then A else X)"
proof-
  {
    assume "A \<prec> T"
    with assms have "A {is closed in} (CoCardinal X T)" using closed_sets_cocardinal by auto
    with assms(2) have "A\<in> {D \<in> Pow(X). D {is closed in} (CoCardinal X T) \<and> A\<subseteq>D}" by auto
    with assms(1) have S:"A\<in>ClosedCovers(A,(CoCardinal X T))" using ClosedCovers_def
      using union_cocardinal by auto
    hence l1:"\<Inter>ClosedCovers(A,(CoCardinal X T))\<subseteq>A" by blast
    from S have l2:"A\<subseteq>\<Inter>ClosedCovers(A,(CoCardinal X T))" 
        using ClosedCovers_def[where T="CoCardinal X T" and A="A"] by auto
    from l1 l2 have "Closure(A,(CoCardinal X T))=A" using Closure_def
      by auto
  }
  moreover
  {
    assume as:"\<not> A \<prec> T"
    {
      fix U
      assume "A\<subseteq>U"
      then have Q:"A \<lesssim> U" using subset_imp_lepoll by auto
      {
        assume "U\<prec> T"
        with Q have "A\<prec> T" using lesspoll_trans1 by auto
        with as have "False" by auto
      }
      hence "\<not> U \<prec> T" by auto
      with assms(1) have "\<not>(U {is closed in} (CoCardinal X T)) \<or> U=X" using closed_sets_cocardinal
      by auto
    }
    with assms(1) have "\<forall>U\<in>Pow(X). U{is closed in}(CoCardinal X T)\<and>A\<subseteq>U\<longrightarrow>U=X"
      by auto
    with assms(1) have "ClosedCovers(A,(CoCardinal X T))\<subseteq>{X}" 
      using union_cocardinal using ClosedCovers_def by auto
    with assms have "ClosedCovers(A,(CoCardinal X T))={X}" using X_closedcov_cocardinal
      by auto
    then have " Closure(A, CoCardinal X T) = X " using Closure_def by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>The boundary of a set is \<open>0\<close> if $A$ and $X-A$ are closed,
 \<open>X\<close> if not $A$ neither $X-A$ are closed and; if only one is closed,
then the closed one is its boundary.\<close>

lemma boundary_cocardinal:
  assumes "T\<noteq>0""A \<subseteq>X"
  shows "Boundary(A,(CoCardinal X T))=(if A\<prec> T then (if  (X-A)\<prec> T then 0 else A) else (if  (X-A)\<prec> T then X-A else X))"
proof-
  {
    assume AS:"A\<prec> T""X-A\<prec> T"
    from AS(2) assms have "Closure(X-A,(CoCardinal X T))=X-A" using closure_set_cocardinal[where A="X-A" and T="T" and X="X"] by auto
    moreover
    from AS(1) assms have "Closure(A,(CoCardinal X T))=A"
      using closure_set_cocardinal by auto
    with calculation assms(1) have "Boundary(A,(CoCardinal X T))=0"using Boundary_def using
      union_cocardinal by auto
  }
  moreover
  {
    assume AS:"~(A\<prec> T)""X-A\<prec> T"
    from AS(2) assms have "Closure(X-A,(CoCardinal X T))=X-A" using closure_set_cocardinal[where A="X-A" and T="T" and X="X"] by auto
    moreover
    from AS(1) assms have "Closure(A,(CoCardinal X T))=X"
      using closure_set_cocardinal by auto
    with calculation assms(1)  have "Boundary(A,(CoCardinal X T))=X-A" using Boundary_def
      union_cocardinal by auto
  }
  moreover
  {
    assume AS:"~(A\<prec> T)""~(X-A\<prec> T)"
    from AS(2) assms have "Closure(X-A,(CoCardinal X T))=X" using closure_set_cocardinal[where A="X-A" and T="T" and X="X"] by auto
    moreover
    from AS(1) assms have "Closure(A,(CoCardinal X T))=X"
      using closure_set_cocardinal by auto
    with calculation assms(1)  have "Boundary(A,(CoCardinal X T))=X"using Boundary_def
      union_cocardinal by auto
  }
  moreover
  {
    assume AS:"A\<prec> T""~(X-A\<prec> T)"
    from AS(2) assms have "Closure(X-A,(CoCardinal X T))=X" using closure_set_cocardinal[where A="X-A" and T="T" and X="X"] by auto
    moreover
    from AS(1) assms have "Closure(A,(CoCardinal X T))=A"
      using closure_set_cocardinal by auto
    with calculation assms have "Boundary(A,(CoCardinal X T))=A" using Boundary_def
      union_cocardinal by auto
  }
  ultimately show ?thesis by auto
qed

subsection\<open>Special cases and subspaces\<close>

text\<open>If the set is too small or the cardinal too large, then the topology
is just the discrete topology.\<close>

lemma discrete_cocardinal:
  assumes "X\<prec> T"
  shows "(CoCardinal X T)=(Pow (X))"
proof
  {
    fix U
    assume "U\<in>(CoCardinal X T)"
    then have "U\<in>Pow (X)" using Cocardinal_def by auto
  }
  then show "(CoCardinal X T)\<subseteq>(Pow (X))" by auto
  {
    fix U
    assume A:"U\<in>Pow(X)"
    then have "X-U \<subseteq> X" by auto
    then have "X-U \<lesssim>X" using subset_imp_lepoll by auto
    then have "X-U\<prec> T" using lesspoll_trans1 assms by auto
    with A have "U\<in>(CoCardinal X T)" using Cocardinal_def
      by auto
  }
  then show "Pow(X)\<subseteq>(CoCardinal X T)" by auto
qed

text\<open>If the cardinal is taken as \<open> T=1 \<close> then the topology
is indiscrete.\<close>

lemma indiscrete_cocardinal:
  shows "(CoCardinal X 1)={0,X}"
proof
  {
    fix Q
    assume "Q\<in>(CoCardinal X 1)"
    then have "Q\<in>Pow(X)""Q=0\<or>X-Q\<prec>1" using Cocardinal_def by auto
    then have "Q\<in>Pow(X)""Q=0\<or>X-Q=0" using lesspoll_succ_iff lepoll_0_iff by (safe,blast)
    then have "Q=0\<or>Q=X" by blast
  }
  then show "(CoCardinal X 1) \<subseteq> {0, X}" by auto
  have "0\<in>(CoCardinal X 1)" using Cocardinal_def by auto
  moreover
  have "0\<prec>1""X-X=0" using lesspoll_succ_iff by auto
  then have "X\<in>(CoCardinal X 1)" using Cocardinal_def by auto
  ultimately show "{0, X} \<subseteq> (CoCardinal X 1) " by auto
qed

text\<open>The topological subspaces of the \<open>CoCardinal X T\<close> topology
are also CoCardinal topologies.\<close>

lemma subspace_cocardinal:
  shows "(CoCardinal X T) {restricted to} Y=(CoCardinal (Y \<inter> X) T)"
proof
  {
    fix M
    assume "M\<in>((CoCardinal X T) {restricted to} Y)"
    then obtain A where A1:"A:(CoCardinal X T)" "M=Y \<inter> A" using RestrictedTo_def by auto
    then have "M\<in>Pow(X \<inter> Y)" using Cocardinal_def by auto
    moreover
    from A1 have "(Y \<inter> X)-M=(Y \<inter> X)-A" using Cocardinal_def by auto
    have "(Y \<inter> X)-A \<subseteq> X-A" by blast
    with \<open>(Y \<inter> X)-M=(Y \<inter> X)-A\<close> have "(Y \<inter> X)-M\<subseteq> X-A" by auto
    then have "(Y \<inter> X)-M \<lesssim> X-A" using subset_imp_lepoll by auto
    with A1 have "(Y \<inter> X)-M \<prec> T \<or> M=0" using lesspoll_trans1 using Cocardinal_def
      by (cases "A=0",simp,cases "Y \<inter> A=0",simp+)
    ultimately have "M\<in>(CoCardinal (Y \<inter> X) T)" using Cocardinal_def
      by auto
  }
  then show "(CoCardinal X T) {restricted to} Y \<subseteq>(CoCardinal (Y \<inter> X) T)" by auto
  {
    fix M
    let ?A="M \<union> (X-Y)"
    assume A:"M\<in>(CoCardinal (Y \<inter> X) T)"
    {
      assume "M=0"
      hence "M=0 \<inter> Y" by auto
      then have "M\<in>(CoCardinal X T) {restricted to} Y" using RestrictedTo_def
        Cocardinal_def by auto
    }
    moreover
    {
      assume AS:"M\<noteq>0"
      from A AS have A1:"(M\<in>Pow(Y \<inter> X) \<and> (Y \<inter> X)-M\<prec> T)" using Cocardinal_def by auto
      hence "?A\<in>Pow(X)" by blast
      moreover
      have "X-?A=(Y \<inter> X)-M" by blast
      with A1 have "X-?A\<prec> T" by auto
      ultimately have "?A\<in>(CoCardinal X T)" using Cocardinal_def by auto
      then have AT:"Y \<inter> ?A\<in>(CoCardinal X T) {restricted to} Y" using RestrictedTo_def
        by auto
      have "Y \<inter> ?A=Y \<inter> M" by blast
      also with A1 have "\<dots>=M" by auto
      finally have "Y \<inter> ?A=M".
      with AT have "M\<in>(CoCardinal X T) {restricted to} Y"
        by auto
    }
    ultimately have "M\<in>(CoCardinal X T) {restricted to} Y" by auto
  }
  then show "(CoCardinal (Y \<inter> X) T) \<subseteq> (CoCardinal X T) {restricted to} Y" by auto
qed

subsection\<open>Excluded Set Topology\<close>

text\<open>In this seccion, we consider all the subsets of a set
which have empty intersection with a fixed set.\<close>

subsection\<open>Excluded set topology is a topology.\<close>

definition
   ExcludedSet ("ExcludedSet _ _" 50) where
   "ExcludedSet X U \<equiv> {F\<in>Pow(X). U \<inter> F=0}\<union> {X}"

text\<open>For any set; we prove that
\<open>ExcludedSet X Q\<close> forms a topology.\<close>

theorem excludedset_is_topology:
  shows "(ExcludedSet X Q) {is a topology}"
proof-
  {
    fix M
    assume "M\<in>Pow(ExcludedSet X Q)"
    then have A:"M\<subseteq>{F\<in>Pow(X). Q \<inter> F=0}\<union> {X}" using ExcludedSet_def by auto
    hence "\<Union>M\<in>Pow(X)" by auto
    moreover
    {
      have B:"Q \<inter>\<Union>M=\<Union>{Q \<inter>T. T\<in>M}" by auto
      {
        assume "X\<notin>M"
        with A have "M\<subseteq>{F\<in>Pow(X). Q \<inter> F=0}" by auto
        with B have "Q \<inter> \<Union>M=0" by auto
      }
      moreover
      {
        assume "X\<in>M"
        with A have "\<Union>M=X" by auto
      }
      ultimately have  "Q \<inter> \<Union>M=0 \<or> \<Union>M=X" by auto
    }
    ultimately have "\<Union>M\<in>(ExcludedSet X Q)" using ExcludedSet_def by auto
  }
  moreover
  {
    fix U V
    assume "U\<in>(ExcludedSet X Q)" "V\<in>(ExcludedSet X Q)"
    then have "U\<in>Pow(X)""V\<in>Pow(X)""U=X\<or> U \<inter> Q=0""V=X\<or> V \<inter> Q=0" using ExcludedSet_def by auto
    hence "U\<in>Pow(X)""V\<in>Pow(X)""(U \<inter> V)=X \<or> Q\<inter>(U \<inter> V)=0" by auto
    then have "(U \<inter> V)\<in>(ExcludedSet X Q)" using ExcludedSet_def by auto
  }
  ultimately show ?thesis using IsATopology_def by auto
qed

theorem topology0_excludedset:
  shows "topology0(ExcludedSet X T)"
  using topology0_def excludedset_is_topology by auto

text\<open>Choosing a singleton set, it is considered a point excluded
topology.\<close>

definition
  ExcludedPoint ("ExcludedPoint _ _" 90) where
  "ExcludedPoint X p\<equiv> ExcludedSet X {p}"

subsection\<open>Total set, Closed sets, Interior, Closure and Boundary\<close>

text\<open>The topology is defined in the set $X$\<close>

lemma union_excludedset:
  shows "\<Union> (ExcludedSet X T)=X"
proof-
  have "X\<in>(ExcludedSet X T)" using ExcludedSet_def by auto
  then show ?thesis using ExcludedSet_def by auto
qed

text\<open>The closed sets are those which contain the set \<open>(X \<inter> T)\<close> and \<open>0\<close>.\<close>

lemma closed_sets_excludedset:
  shows "D {is closed in} (ExcludedSet X T) \<longleftrightarrow> (D\<in>Pow(X) & (X \<inter> T) \<subseteq>D)\<or> D=0"
proof-
  {
    fix x
    assume A:"D \<subseteq> X" "X - D \<in> (ExcludedSet X T) "" D \<noteq> 0""x:T""x:X"
    from A(1) have B:"X-(X-D)=D" by auto
    from A(2) have "T\<inter>(X-D)=0\<or> X-D=X" using ExcludedSet_def by auto
    hence "T\<inter>(X-D)=0\<or> X-(X-D)=X-X" by auto
    with B have "T\<inter>(X-D)=0\<or> D=X-X" by auto
    hence "T\<inter>(X-D)=0\<or> D=0" by auto
    with A(3) have "T\<inter>(X-D)=0" by auto
    with A(4) have "x\<notin>X-D" by auto
    with A(5) have "x\<in>D" by auto
  }
  moreover
  {
    assume A:"X\<inter>T\<subseteq>D""D\<subseteq>X"
    from A(1) have "X-D\<subseteq>X-(X\<inter>T)" by auto
    also have "\<dots>=X-T" by auto
    finally have "T\<inter>(X-D)=0" by auto
    moreover
    have "X-D\<in>Pow(X)" by auto
    ultimately have "X-D\<in>(ExcludedSet X T)" using ExcludedSet_def by auto
  }
  ultimately show ?thesis using IsClosed_def union_excludedset
    ExcludedSet_def by auto
qed

text\<open>The interior of a set is itself if it is \<open>X\<close> or
the difference with the set \<open>T\<close>\<close>

lemma interior_set_excludedset:
  assumes "A\<subseteq>X"
  shows "Interior(A,(ExcludedSet X T))= (if A=X then X else A-T)"
proof-
  {
    assume A:"A\<noteq>X"
    from assms have "A-T\<in>(ExcludedSet X T)" using ExcludedSet_def by auto
    then have "A-T\<subseteq>Interior(A,(ExcludedSet X T))"
    using Interior_def by auto
    moreover
    {
      fix U
      assume "U\<in>(ExcludedSet X T)""U\<subseteq>A"
      then have "T\<inter>U=0 \<or> U=X""U\<subseteq>A" using ExcludedSet_def by auto
      with A assms have "T\<inter>U=0""U\<subseteq>A" by auto
      then have "U-T=U""U-T\<subseteq>A-T" by (safe,blast+)
      then have "U\<subseteq>A-T" by auto
    }
    then have "Interior(A,(ExcludedSet X T))\<subseteq>A-T" using Interior_def by auto
    ultimately have "Interior(A,(ExcludedSet X T))=A-T" by auto
  }
  moreover
  have "X\<in>(ExcludedSet X T)" using ExcludedSet_def
  union_excludedset by auto
  then have "Interior(X,(ExcludedSet X T))=X" using topology0.Top_2_L3
  topology0_excludedset by auto
  ultimately show ?thesis by auto
qed

text\<open>The closure of a set is itself if it is \<open>0\<close> or
the union with \<open>T\<close>.\<close>

lemma closure_set_excludedset:
  assumes "A\<subseteq>X"
  shows "Closure(A,(ExcludedSet X T))=(if A=0 then 0 else A \<union>(X\<inter> T))"
proof-
  have "0\<in>ClosedCovers(0,(ExcludedSet X T))" using ClosedCovers_def
    closed_sets_excludedset by auto
  then have "Closure(0,(ExcludedSet X T))\<subseteq>0" using Closure_def by auto
  hence "Closure(0,(ExcludedSet X T))=0" by blast
  moreover
  {
    assume A:"A\<noteq>0"
    then have "(A \<union>(X\<inter> T)) {is closed in} (ExcludedSet X T)" 
      using closed_sets_excludedset[of "A \<union>(X\<inter> T)"] assms A 
      by blast
    then have "(A \<union>(X\<inter> T))\<in> {D \<in> Pow(X). D {is closed in} (ExcludedSet X T) \<and> A\<subseteq>D}"
    using assms by auto
    then have "(A \<union>(X\<inter> T))\<in>ClosedCovers(A,(ExcludedSet X T))" unfolding ClosedCovers_def
    using union_excludedset by auto
    then have l1:"\<Inter>ClosedCovers(A,(ExcludedSet X T))\<subseteq>(A \<union>(X\<inter> T))" by blast
    {
      fix U
      assume "U\<in>ClosedCovers(A,(ExcludedSet X T))"
      then have "U{is closed in}(ExcludedSet X T)""A\<subseteq>U" using ClosedCovers_def
       union_excludedset by auto
      then have "U=0\<or>(X\<inter>T)\<subseteq>U""A\<subseteq>U" using closed_sets_excludedset
       by auto
      then have "(X\<inter>T)\<subseteq>U""A\<subseteq>U" using A by auto
      then have "(X\<inter>T)\<union>A\<subseteq>U" by auto
    }
    then have "(A \<union>(X\<inter> T))\<subseteq>\<Inter>ClosedCovers(A,(ExcludedSet X T))" using topology0.Top_3_L3
      topology0_excludedset union_excludedset assms by auto
    with l1 have "\<Inter>ClosedCovers(A,(ExcludedSet X T))=(A \<union>(X\<inter> T))" by auto
    then have "Closure(A, ExcludedSet X T) = (A \<union>(X\<inter> T)) "
    using Closure_def by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>The boundary of a set is \<open>0\<close> if $A$ is \<open>X\<close>
or \<open>0\<close>, and \<open>X\<inter>T\<close> in other case.\<close>

lemma boundary_excludedset:
  assumes "A \<subseteq>X"
  shows "Boundary(A,(ExcludedSet X T))=(if A=0\<or>A=X then 0 else X\<inter>T)"
proof-
  {
    have "Closure(0,(ExcludedSet X T))=0""Closure(X - 0,(ExcludedSet X T))=X"
    using closure_set_excludedset by auto
    then have "Boundary(0,(ExcludedSet X T))=0"using Boundary_def using
      union_excludedset assms by auto
  }
  moreover
  {
    have "X-X=0" by blast
    then have "Closure(X,(ExcludedSet X T))=X""Closure(X-X,(ExcludedSet X T))=0"
    using closure_set_excludedset by auto
    then have "Boundary(X,(ExcludedSet X T))=0"unfolding Boundary_def using
      union_excludedset by auto
  }
  moreover
  {
    assume AS:"(A\<noteq>0)\<and>(A\<noteq>X)"
    then have "(A\<noteq>0)""(X-A\<noteq>0)" using assms by (safe,blast)
    then have "Closure(A,(ExcludedSet X T))=A \<union> (X\<inter>T)""Closure(X-A,(ExcludedSet X T))=(X-A) \<union> (X\<inter>T)"
    using closure_set_excludedset[where A="A" and X="X"] assms closure_set_excludedset[where A="X-A"
      and X="X"] by auto
    then have "Boundary(A,(ExcludedSet X T))=X\<inter>T" unfolding Boundary_def using
      union_excludedset by auto
  }
  ultimately show ?thesis by auto
qed

subsection\<open>Special cases and subspaces\<close>

text\<open>The topology is equal in the sets \<open>T\<close> and  
\<open>X\<inter>T\<close>.\<close>

lemma smaller_excludedset:
  shows "(ExcludedSet X T)=(ExcludedSet X (X\<inter>T))"
  using ExcludedSet_def by (simp,blast)

text\<open>If the set which is excluded is disjoint with \<open>X\<close>,
then the topology is discrete.\<close>

lemma empty_excludedset:
  assumes "T\<inter>X=0"
  shows "(ExcludedSet X T)=Pow(X)"
  using smaller_excludedset assms ExcludedSet_def by (simp,blast)

text\<open>The topological subspaces of the \<open>ExcludedSet X T\<close> topology
are also ExcludedSet topologies.\<close>

lemma subspace_excludedset:
  shows "(ExcludedSet X T) {restricted to} Y=(ExcludedSet (Y \<inter> X) T)"
proof
  {
    fix M
    assume "M\<in>((ExcludedSet X T) {restricted to} Y)"
    then obtain A where A1:"A:(ExcludedSet X T)" "M=Y \<inter> A" unfolding RestrictedTo_def by auto
    then have "M\<in>Pow(X \<inter> Y)" unfolding ExcludedSet_def by auto
    moreover
    from A1 have "T\<inter>M=0\<or>M=Y\<inter>X" unfolding ExcludedSet_def by blast
    ultimately have "M\<in>(ExcludedSet (Y \<inter> X) T)" unfolding ExcludedSet_def
      by auto
  }
  then show "(ExcludedSet X T) {restricted to} Y \<subseteq>(ExcludedSet (Y \<inter> X) T)" by auto
  {
    fix M
    let ?A="M \<union> ((X\<inter>Y-T)-Y)"
    assume A:"M\<in>(ExcludedSet (Y \<inter> X) T)"
    {
      assume "M=Y \<inter> X"
      then have "M\<in>(ExcludedSet X T) {restricted to} Y" unfolding RestrictedTo_def
        ExcludedSet_def by auto
    }
    moreover
    {
      assume AS:"M\<noteq>Y \<inter> X"
      from A AS have A1:"(M\<in>Pow(Y \<inter> X) \<and> T\<inter>M=0)" unfolding ExcludedSet_def by auto
      then have "?A\<in>Pow(X)" by blast
      moreover
      have "T\<inter>?A=T\<inter>M" by blast
      with A1 have "T\<inter>?A=0" by auto
      ultimately have "?A\<in>(ExcludedSet X T)" unfolding ExcludedSet_def by auto
      then have AT:"Y \<inter> ?A\<in>(ExcludedSet X T) {restricted to} Y"unfolding RestrictedTo_def
        by auto
      have "Y \<inter> ?A=Y \<inter> M" by blast
      also have "\<dots>=M" using A1 by auto
      finally have "Y \<inter> ?A=M".
      then have "M\<in>(ExcludedSet X T) {restricted to} Y" using AT
        by auto
    }
    ultimately have "M\<in>(ExcludedSet X T) {restricted to} Y" by auto
  }
  then show "(ExcludedSet (Y \<inter> X) T) \<subseteq> (ExcludedSet X T) {restricted to} Y" by auto
qed

subsection\<open>Included Set Topology\<close>

text\<open>In this section we consider the subsets of a set which
contain a fixed set.\<close>

text\<open>The family defined in this section and the one in the previous section are
dual; meaning that the closed set of one are the open sets of the other.\<close>

subsection\<open>Included set topology is a topology.\<close>

definition 
  IncludedSet ("IncludedSet _ _" 50) where
  "IncludedSet X U \<equiv> {F\<in>Pow(X). U \<subseteq> F}\<union> {0}"

text\<open>For any set; we prove that
\<open>IncludedSet X Q\<close> forms a topology.\<close>

theorem includedset_is_topology:
  shows "(IncludedSet X Q) {is a topology}"
proof-
  {
    fix M
    assume "M\<in>Pow(IncludedSet X Q)"
    then have A:"M\<subseteq>{F\<in>Pow(X). Q \<subseteq> F}\<union> {0}" using IncludedSet_def by auto
    then have "\<Union>M\<in>Pow(X)" by auto
    moreover
    have"Q \<subseteq>\<Union>M\<or> \<Union>M=0" using A by blast
    ultimately have "\<Union>M\<in>(IncludedSet X Q)" using IncludedSet_def by auto
  }
  moreover
  {
    fix U V
    assume "U\<in>(IncludedSet X Q)" "V\<in>(IncludedSet X Q)"
    then have "U\<in>Pow(X)""V\<in>Pow(X)""U=0\<or> Q\<subseteq>U""V=0\<or> Q\<subseteq>V" using IncludedSet_def by auto
    then have "U\<in>Pow(X)""V\<in>Pow(X)""(U \<inter> V)=0 \<or> Q\<subseteq>(U \<inter> V)" by auto
    then have "(U \<inter> V)\<in>(IncludedSet X Q)" using IncludedSet_def by auto
  }
  ultimately show ?thesis using IsATopology_def by auto
qed

theorem topology0_includedset:
  shows "topology0(IncludedSet X T)"
  using topology0_def includedset_is_topology by auto

text\<open>Choosing a singleton set, it is considered a point excluded
topology. In the following lemmas and theorems, when neccessary
it will be considered that \<open> T\<noteq>0 \<close> and \<open> T\<subseteq>X \<close>.
Theese cases will appear in the special cases section.\<close>

definition
  IncludedPoint ("IncludedPoint _ _" 90) where
  "IncludedPoint X p\<equiv> IncludedSet X {p}"

subsection\<open>Total set, Closed sets, Interior, Closure and Boundary\<close>

text\<open>The topology is defined in the set $X$.\<close>

lemma union_includedset:
  assumes "T\<subseteq>X "
  shows "\<Union> (IncludedSet X T)=X"
proof-
  from assms have "X\<in>(IncludedSet X T)" using IncludedSet_def by auto
  then show "\<Union> (IncludedSet X T)=X" using IncludedSet_def by auto
qed

text\<open>The closed sets are those which are disjoint with \<open>T\<close>
 and \<open>X\<close>.\<close>

lemma closed_sets_includedset:
  assumes "T\<subseteq>X"
  shows "D {is closed in} (IncludedSet X T) \<longleftrightarrow> (D\<in>Pow(X) & (D \<inter> T)=0)\<or> D=X"
proof-
  have "X-X=0" by blast
  then have "X-X\<in>(IncludedSet X T)" using IncludedSet_def by auto
  moreover
  {
    assume A:"D \<subseteq> X" "X - D \<in> (IncludedSet X T) "" D \<noteq> X"
    from A(2) have "T\<subseteq>(X-D)\<or> X-D=0" using IncludedSet_def by auto
    with A(1) have "T\<subseteq>(X-D)\<or> D=X" by blast 
    with A(3) have "T\<subseteq>(X-D)" by auto
    hence "D\<inter>T=0" by blast
  }
  moreover
  {
    assume A:"D\<inter>T=0""D\<subseteq>X"
    from A(1) assms have "T\<subseteq>(X-D)" by blast
    then have "X-D\<in>(IncludedSet X T)" using IncludedSet_def by auto
  }
  ultimately show ?thesis using IsClosed_def union_includedset assms by auto
qed

text\<open>The interior of a set is itself if it is open or
 \<open>0\<close> if it isn't.\<close>

lemma interior_set_includedset:
  assumes "A\<subseteq>X"
  shows "Interior(A,(IncludedSet X T))= (if T\<subseteq>A then A else 0)"
proof-
  {
    fix x
    assume A:"Interior(A, IncludedSet X T) \<noteq> 0 ""x\<in>T"
    have "Interior(A,IncludedSet X T)\<in>(IncludedSet X T)" using
      topology0.Top_2_L2 topology0_includedset by auto
    with A(1) have "T\<subseteq>Interior(A, IncludedSet X T)" using IncludedSet_def
      by auto
    with A(2) have "x\<in>Interior(A, IncludedSet X T)" by auto
    then have "x\<in>A" using topology0.Top_2_L1 topology0_includedset by auto}
    moreover
  {
    assume "T\<subseteq>A"
    with assms have "A\<in>(IncludedSet X T)" using IncludedSet_def by auto
    then have "Interior(A,IncludedSet X T)=A" using topology0.Top_2_L3
      topology0_includedset by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>The closure of a set is itself if it is closed or
 \<open>X\<close> if it isn't.\<close>

lemma closure_set_includedset:
  assumes "A\<subseteq>X""T\<subseteq>X"
  shows "Closure(A,(IncludedSet X T))= (if T\<inter>A=0 then A else X)"
proof-
  {
    assume AS:"T\<inter>A=0"
    then have "A {is closed in} (IncludedSet X T)" using closed_sets_includedset
      assms by auto
    with assms(1) have "Closure(A,(IncludedSet X T))=A" using topology0.Top_3_L8
      topology0_includedset union_includedset assms(2) by auto
  }
  moreover
  {
    assume AS:"T\<inter>A\<noteq>0"
    have "X\<in>ClosedCovers(A,(IncludedSet X T))" using ClosedCovers_def
      closed_sets_includedset union_includedset assms by auto
    then have l1:"\<Inter>ClosedCovers(A,(IncludedSet X T))\<subseteq>X" using Closure_def
      by auto
    moreover
    {
      fix U
      assume "U\<in>ClosedCovers(A,(IncludedSet X T))"  
      then have "U{is closed in}(IncludedSet X T)""A\<subseteq>U" using ClosedCovers_def
        by auto
      then have "U=X\<or>(T\<inter>U)=0""A\<subseteq>U" using closed_sets_includedset assms(2)
        by auto
      then have "U=X\<or>(T\<inter>A)=0" by auto
      then have "U=X" using AS by auto
    }
    then have "X\<subseteq>\<Inter>ClosedCovers(A,(IncludedSet X T))" using topology0.Top_3_L3
      topology0_includedset union_includedset assms by auto
    ultimately have "\<Inter>ClosedCovers(A,(IncludedSet X T))=X" by auto
    then have "Closure(A, IncludedSet X T) = X "
      using Closure_def by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>The boundary of a set is \<open>X-A\<close> if $A$ contains \<open>T\<close>
completely, is \<open>A\<close> if $X-A$ contains \<open>T\<close>
completely
and \<open>X\<close> if \<open>T\<close> is divided between the two sets.
The case where \<open> T=0 \<close> is considered as an special case.\<close>

lemma boundary_includedset:
  assumes "A \<subseteq>X""T \<subseteq>X""T\<noteq>0"
  shows "Boundary(A,(IncludedSet X T))=(if T\<subseteq>A then X-A else (if T\<inter>A=0 then A else X))"
proof-
  {
    assume AS:"(T\<subseteq>A)"
    then have "T\<inter>A\<noteq>0""T\<inter>(X-A)=0" using assms(2,3) by (auto,blast)
    then have "Closure(A,(IncludedSet X T))=X""Closure(X-A,(IncludedSet X T))=(X-A)"
      using closure_set_includedset[where A="A" and X="X"and T="T"] assms(1,2) closure_set_includedset[where A="X-A"
      and X="X"and T="T"] by auto
    then have "Boundary(A,(IncludedSet X T))=X-A" unfolding Boundary_def using
      union_includedset assms(2) by auto
  }
  moreover
  {
    assume AS:"~(T\<subseteq>A)""T\<inter>A=0"
    then have "T\<inter>A=0""T\<inter>(X-A)\<noteq>0" using assms(2) by (safe,blast+)
    then have "Closure(A,(IncludedSet X T))=A""Closure(X-A,(IncludedSet X T))=X"
      using closure_set_includedset[where A="A" and X="X"and T="T"] assms(1,2) closure_set_includedset[where A="X-A"
      and X="X"and T="T"] by auto
    then have "Boundary(A,(IncludedSet X T))=A" unfolding Boundary_def using
      union_includedset assms(1,2) by auto
  }
  moreover
  {
    assume AS:"~(T\<subseteq>A)""T\<inter>A\<noteq>0"
    then have "T\<inter>A\<noteq>0""T\<inter>(X-A)\<noteq>0" using assms(2) by (safe,blast+)
    then have "Closure(A,(IncludedSet X T))=X""Closure(X-A,(IncludedSet X T))=X"
      using closure_set_includedset[where A="A" and X="X"and T="T"] assms(1,2) closure_set_includedset[where A="X-A"
      and X="X"and T="T"] by auto
    then have "Boundary(A,(IncludedSet X T))=X" unfolding Boundary_def using
      union_includedset assms(2) by auto
  }
  ultimately show ?thesis by auto
qed

subsection\<open>Special cases and subspaces\<close>

text\<open>The topology is discrete if \<open> T=0 \<close>\<close>

lemma smaller_includedset:
  shows "(IncludedSet X 0)=Pow(X)"
  using IncludedSet_def by (simp,blast)

text\<open>If the set which is included is not a subset of \<open>X\<close>,
then the topology is trivial.\<close>

lemma empty_includedset:
  assumes "~(T\<subseteq>X)"
  shows "(IncludedSet X T)={0}"
  using assms IncludedSet_def by (simp,blast)

text\<open>The topological subspaces of the \<open>IncludedSet X T\<close> topology
are also IncludedSet topologies. The trivial case does not fit the idea
in the demonstration;
because if \<open> Y\<subseteq>X \<close>  then \<open>IncludedSet (Y \<inter> X) (Y\<inter>T)\<close>
is never trivial. There is no need of a separate proof because
the only subspace of the trivial topology is itself.\<close>

lemma subspace_includedset:
  assumes "T\<subseteq>X"
  shows "(IncludedSet X T) {restricted to} Y=(IncludedSet (Y \<inter> X) (Y\<inter>T))"
proof
  {
    fix M
    assume "M\<in>((IncludedSet X T) {restricted to} Y)"
    then obtain A where A1:"A:(IncludedSet X T)" "M=Y \<inter> A" unfolding RestrictedTo_def by auto
    then have "M\<in>Pow(X \<inter> Y)" unfolding IncludedSet_def by auto
    moreover
    from A1 have "Y\<inter>T\<subseteq>M\<or>M=0" unfolding IncludedSet_def by blast
    ultimately have "M\<in>(IncludedSet (Y \<inter> X) (Y\<inter>T))" unfolding IncludedSet_def
      by auto
  }
  then show "(IncludedSet X T) {restricted to} Y \<subseteq>(IncludedSet (Y \<inter> X) (Y\<inter>T))" by auto
  {
    fix M
    let ?A="M \<union> T"
    assume A:"M\<in>(IncludedSet (Y \<inter> X) (Y\<inter>T))"
    {
      assume "M=0"
      then have "M\<in>(IncludedSet X T) {restricted to} Y" unfolding RestrictedTo_def
        IncludedSet_def by auto
    }
    moreover
    {
      assume AS:"M\<noteq>0"
      from A AS have A1:"(M\<in>Pow(Y \<inter> X) \<and> Y \<inter>T\<subseteq>M)" unfolding IncludedSet_def by auto
      then have "?A\<in>Pow(X)" using assms by blast
      moreover
      have "T\<subseteq>?A" by blast
      ultimately have "?A\<in>(IncludedSet X T)" unfolding IncludedSet_def by auto
      then have AT:"Y \<inter> ?A\<in>(IncludedSet X T) {restricted to} Y"unfolding RestrictedTo_def
        by auto
      from A1 have "Y \<inter> ?A=Y \<inter> M" by blast
      also with A1 have "\<dots>=M" by auto
      finally have "Y \<inter> ?A=M".
      with AT have "M\<in>(IncludedSet X T) {restricted to} Y"
        by auto
    }
    ultimately have "M\<in>(IncludedSet X T) {restricted to} Y" by auto
  }
  thus "(IncludedSet (Y \<inter> X) (Y \<inter> T)) \<subseteq> (IncludedSet X T) {restricted to} Y" by auto
qed

end
