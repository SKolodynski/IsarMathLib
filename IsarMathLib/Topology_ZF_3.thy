(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2011, 2012  Slawomir Kolodynski

    This program is free software Redistribution and use in source and binary forms, 
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

section \<open>Topology 3\<close>

theory Topology_ZF_3 imports Topology_ZF_2 FiniteSeq_ZF

begin

text\<open>\<open>Topology_ZF_1\<close> theory describes how we can define  a topology on a product
of two topological spaces. One way to generalize that is to construct topology for a cartesian
product of $n$ topological spaces. The cartesian product approach is somewhat inconvenient though.
Another way to approach product topology on $X^n$ is to model cartesian product as sets of 
sequences (of length $n$) of elements of $X$. This means that having a topology on $X$ we want
to define a toplogy on the space $n\rightarrow X$, where $n$ is a natural number (recall that 
$n = \{ 0,1,...,n-1\}$ in ZF). However, this in turn can be done more generally by defining a 
topology on any function space $I\rightarrow X$, where $I$ is any set of indices. This is what we 
do in this theory.\<close>

subsection\<open>The base of the product topology\<close>

text\<open>In this section we define the base of the product topology.\<close>

text\<open>Suppose $\mathcal{X} = I\rightarrow \bigcup T$ is a space of functions from some index set $I$
to the carrier of a topology $T$. Then take a finite collection of open sets $W:N\rightarrow T$ 
indexed by $N\subseteq I$. We can define a subset of $\mathcal{X}$ that models the cartesian product of $W$.
\<close>

definition
  "FinProd(\<X>,W) \<equiv> {x\<in>\<X>. \<forall> i\<in>domain(W). x`(i) \<in> W`(i)}"

text\<open>Now we define the base of the product topology as the collection of all finite products 
(in the sense defined above) of open sets. 
\<close>

definition
  "ProductTopBase(I,T) \<equiv>  \<Union>N\<in>FinPow(I).{FinProd(I\<rightarrow>\<Union>T,W). W\<in>N\<rightarrow>T}"

text\<open>Finally, we define the product topology on sequences. We use the ''Seq'' 
prefix although the definition is good for any index sets, not only natural numbers.\<close>

definition
  "SeqProductTopology(I,T) \<equiv> {\<Union>B. B \<in> Pow(ProductTopBase(I,T))}"

text\<open>Product topology base is closed with respect to intersections.\<close>

lemma prod_top_base_inter: 
  assumes A1: "T {is a topology}" and  
  A2: "U \<in> ProductTopBase(I,T)"  "V \<in> ProductTopBase(I,T)"
  shows "U\<inter>V \<in> ProductTopBase(I,T)"
proof -
  let ?\<X> = "I\<rightarrow>\<Union>T"  
  from A2 obtain N\<^sub>1  W\<^sub>1 N\<^sub>2 W\<^sub>2 where 
    I: "N\<^sub>1 \<in> FinPow(I)"  "W\<^sub>1\<in>N\<^sub>1\<rightarrow>T"  "U = FinProd(?\<X>,W\<^sub>1)" and
    II: "N\<^sub>2 \<in> FinPow(I)"  "W\<^sub>2\<in>N\<^sub>2\<rightarrow>T"  "V = FinProd(?\<X>,W\<^sub>2)"
    using ProductTopBase_def by auto
  let ?N\<^sub>3 = "N\<^sub>1 \<union> N\<^sub>2"
  let ?W\<^sub>3 = "{\<langle>i,if i \<in> N\<^sub>1-N\<^sub>2 then W\<^sub>1`(i) 
        else if i \<in> N\<^sub>2-N\<^sub>1 then  W\<^sub>2`(i) 
        else (W\<^sub>1`(i)) \<inter> (W\<^sub>2`(i))\<rangle>. i \<in> ?N\<^sub>3}"
  from A1 I II have "\<forall>i \<in> N\<^sub>1 \<inter> N\<^sub>2.  (W\<^sub>1`(i) \<inter> W\<^sub>2`(i)) \<in> T"
      using apply_funtype IsATopology_def by auto
  moreover from I II have "\<forall>i\<in>N\<^sub>1-N\<^sub>2. W\<^sub>1`(i) \<in> T" and "\<forall>i\<in>N\<^sub>2-N\<^sub>1. W\<^sub>2`(i) \<in> T" 
      using apply_funtype by auto
  ultimately have  "?W\<^sub>3:?N\<^sub>3\<rightarrow>T" by (rule fun_union_overlap)
  with I II have "FinProd(?\<X>,?W\<^sub>3) \<in> ProductTopBase(I,T)" using union_finpow ProductTopBase_def
    by auto
  moreover have "U\<inter>V = FinProd(?\<X>,?W\<^sub>3)"
  proof
    { fix x assume "x\<in>U" and "x\<in>V"
      with \<open>U = FinProd(?\<X>,W\<^sub>1)\<close>  \<open>W\<^sub>1\<in>N\<^sub>1\<rightarrow>T\<close> and  \<open>V = FinProd(?\<X>,W\<^sub>2)\<close>  \<open>W\<^sub>2\<in>N\<^sub>2\<rightarrow>T\<close>
      have "x\<in>?\<X>" and "\<forall>i\<in>N\<^sub>1. x`(i) \<in> W\<^sub>1`(i)" and "\<forall>i\<in>N\<^sub>2. x`(i) \<in> W\<^sub>2`(i)"
        using func1_1_L1 FinProd_def by auto
      with \<open>?W\<^sub>3:?N\<^sub>3\<rightarrow>T\<close> \<open>x\<in>?\<X>\<close> have "x \<in> FinProd(?\<X>,?W\<^sub>3)"  
        using ZF_fun_from_tot_val func1_1_L1 FinProd_def by auto
    } thus "U\<inter>V \<subseteq> FinProd(?\<X>,?W\<^sub>3)" by auto
    { fix x assume "x \<in> FinProd(?\<X>,?W\<^sub>3)"
      with \<open>?W\<^sub>3:?N\<^sub>3\<rightarrow>T\<close> have "x:I\<rightarrow>\<Union>T" and III: "\<forall>i\<in>?N\<^sub>3. x`(i) \<in> ?W\<^sub>3`(i)"
        using FinProd_def func1_1_L1 by auto
     { fix i assume "i\<in>N\<^sub>1" 
       with \<open>?W\<^sub>3:?N\<^sub>3\<rightarrow>T\<close> have "?W\<^sub>3`(i) \<subseteq> W\<^sub>1`(i)" using ZF_fun_from_tot_val by auto
       with III \<open>i\<in>N\<^sub>1\<close> have "x`(i) \<in> W\<^sub>1`(i)" by auto
     } with \<open>W\<^sub>1\<in>N\<^sub>1\<rightarrow>T\<close> \<open>x:I\<rightarrow>\<Union>T\<close> \<open>U = FinProd(?\<X>,W\<^sub>1)\<close> 
      have "x \<in> U" using func1_1_L1 FinProd_def by auto
      moreover
      { fix i assume "i\<in>N\<^sub>2" 
        with \<open>?W\<^sub>3:?N\<^sub>3\<rightarrow>T\<close> have "?W\<^sub>3`(i) \<subseteq> W\<^sub>2`(i)" using ZF_fun_from_tot_val by auto
        with III \<open>i\<in>N\<^sub>2\<close> have "x`(i) \<in> W\<^sub>2`(i)" by auto
      } with \<open>W\<^sub>2\<in>N\<^sub>2\<rightarrow>T\<close> \<open>x:I\<rightarrow>\<Union>T\<close> \<open>V = FinProd(?\<X>,W\<^sub>2)\<close> have "x\<in>V" 
          using func1_1_L1 FinProd_def by auto 
      ultimately have "x \<in> U\<inter>V" by simp
    } thus "FinProd(?\<X>,?W\<^sub>3) \<subseteq> U\<inter>V" by auto
  qed
    ultimately show ?thesis by simp
qed 

text\<open>In the next theorem we show the collection of sets defined above as 
\<open>ProductTopBase(\<X>,T)\<close> satisfies the base condition. This is a condition, defined in 
\<open>Topology_ZF_1\<close> that allows to claim that this collection is a base for some topology.\<close>

theorem prod_top_base_is_base: assumes "T {is a topology}" 
  shows "ProductTopBase(I,T) {satisfies the base condition}"
  using assms prod_top_base_inter inter_closed_base by simp

text\<open>The (sequence) product topology is indeed a topology on the space of sequences.
In the proof we are using the fact that $(\emptyset\rightarrow X) = \{\emptyset\}$.\<close>

theorem seq_prod_top_is_top:  assumes "T {is a topology}"
  shows 
  "SeqProductTopology(I,T) {is a topology}" and 
  "ProductTopBase(I,T) {is a base for} SeqProductTopology(I,T)" and
  "\<Union>SeqProductTopology(I,T) = (I\<rightarrow>\<Union>T)"
proof -
  from assms show "SeqProductTopology(I,T) {is a topology}" and 
    I: "ProductTopBase(I,T) {is a base for} SeqProductTopology(I,T)"
      using prod_top_base_is_base SeqProductTopology_def Top_1_2_T1
        by auto
  from I have "\<Union>SeqProductTopology(I,T) = \<Union>ProductTopBase(I,T)"
    using Top_1_2_L5 by simp
  also have "\<Union>ProductTopBase(I,T) = (I\<rightarrow>\<Union>T)"
  proof
    show "\<Union>ProductTopBase(I,T) \<subseteq> (I\<rightarrow>\<Union>T)" using ProductTopBase_def FinProd_def
      by auto
    have "0 \<in> FinPow(I)" using empty_in_finpow by simp
    hence "{FinProd(I\<rightarrow>\<Union>T,W). W\<in>0\<rightarrow>T} \<subseteq> (\<Union>N\<in>FinPow(I).{FinProd(I\<rightarrow>\<Union>T,W). W\<in>N\<rightarrow>T})"
      by blast
    then show "(I\<rightarrow>\<Union>T) \<subseteq> \<Union>ProductTopBase(I,T)" using ProductTopBase_def FinProd_def
      by auto
  qed     
  finally show "\<Union>SeqProductTopology(I,T) = (I\<rightarrow>\<Union>T)" by simp
qed

subsection\<open>Finite product of topologies\<close>

text\<open>As a special case of the space of functions $I\rightarrow X$ we can consider space of lists
of elements of $X$, i.e. space $n\rightarrow X$, where $n$ is a natural number (recall that in ZF 
set theory $n=\{0,1,...,n-1\}$). Such spaces model finite cartesian products $X^n$ 
but are easier to deal with in formalized way (than the said products). 
This section discusses natural topology defined on $n\rightarrow X$ where $X$ is a topological space.
\<close>

text\<open>When the index set is finite, the definition of \<open>ProductTopBase(I,T)\<close> 
can be simplifed.\<close>

lemma fin_prod_def_nat: assumes A1: "n\<in>nat" and A2: "T {is a topology}"  
  shows "ProductTopBase(n,T) = {FinProd(n\<rightarrow>\<Union>T,W). W\<in>n\<rightarrow>T}"
proof
  from A1 have "n \<in> FinPow(n)" using nat_finpow_nat fin_finpow_self by auto
  then show "{FinProd(n\<rightarrow>\<Union>T,W). W\<in>n\<rightarrow>T} \<subseteq> ProductTopBase(n,T)" using ProductTopBase_def
    by auto
  { fix B assume "B \<in> ProductTopBase(n,T)"
    then obtain N W where  "N \<in> FinPow(n)" and "W \<in> N\<rightarrow>T" and "B = FinProd(n\<rightarrow>\<Union>T,W)"
      using ProductTopBase_def by auto
    let ?W\<^sub>n = "{\<langle>i,if i\<in>N then W`(i) else \<Union>T\<rangle>. i\<in>n}"
    from A2  \<open>N \<in> FinPow(n)\<close>  \<open>W\<in>N\<rightarrow>T\<close> have "\<forall>i\<in>n. (if i\<in>N then W`(i) else \<Union>T) \<in> T"
      using apply_funtype FinPow_def IsATopology_def by auto
    then have "?W\<^sub>n:n\<rightarrow>T" by (rule ZF_fun_from_total)
    moreover have "B = FinProd(n\<rightarrow>\<Union>T,?W\<^sub>n)"
    proof
      { fix x assume "x\<in>B"
        with \<open>B = FinProd(n\<rightarrow>\<Union>T,W)\<close> have "x \<in> n\<rightarrow>\<Union>T" using FinProd_def by simp
        moreover have "\<forall>i\<in>domain(?W\<^sub>n). x`(i) \<in> ?W\<^sub>n`(i)"
        proof
          fix i assume "i \<in> domain(?W\<^sub>n)"
          with \<open>?W\<^sub>n:n\<rightarrow>T\<close> have "i\<in>n" using func1_1_L1 by simp 
          with \<open>x:n\<rightarrow>\<Union>T\<close> have "x`(i) \<in> \<Union>T" using apply_funtype by blast
          with \<open>x\<in>B\<close> \<open>B = FinProd(n\<rightarrow>\<Union>T,W)\<close> \<open>W \<in> N\<rightarrow>T\<close> \<open>?W\<^sub>n:n\<rightarrow>T\<close> \<open>i\<in>n\<close>
          show "x`(i) \<in> ?W\<^sub>n`(i)" using func1_1_L1 FinProd_def ZF_fun_from_tot_val 
            by simp
        qed
        ultimately have "x \<in> FinProd(n\<rightarrow>\<Union>T,?W\<^sub>n)" using FinProd_def by simp
      } thus "B \<subseteq> FinProd(n\<rightarrow>\<Union>T,?W\<^sub>n)" by auto
      next
      { fix x assume "x \<in> FinProd(n\<rightarrow>\<Union>T,?W\<^sub>n)"    
        then have "x \<in> n\<rightarrow>\<Union>T" and "\<forall>i\<in>domain(?W\<^sub>n). x`(i) \<in> ?W\<^sub>n`(i)" 
          using  FinProd_def by auto
        with \<open>?W\<^sub>n:n\<rightarrow>T\<close> and \<open>N \<in> FinPow(n)\<close> have "\<forall>i\<in>N. x`(i) \<in> ?W\<^sub>n`(i)"
          using func1_1_L1 FinPow_def by auto
        moreover from \<open>?W\<^sub>n:n\<rightarrow>T\<close> and \<open>N \<in> FinPow(n)\<close> 
        have "\<forall>i\<in>N. ?W\<^sub>n`(i) = W`(i)"
          using ZF_fun_from_tot_val FinPow_def by auto
        ultimately have "\<forall>i\<in>N. x`(i) \<in> W`(i)" by simp
        with \<open>W \<in> N\<rightarrow>T\<close> \<open>x \<in> n\<rightarrow>\<Union>T\<close> \<open>B = FinProd(n\<rightarrow>\<Union>T,W)\<close> have "x\<in>B"
          using func1_1_L1 FinProd_def by simp
     } thus "FinProd(n\<rightarrow>\<Union>T,?W\<^sub>n) \<subseteq> B" by auto
  qed 
    ultimately have "B \<in> {FinProd(n\<rightarrow>\<Union>T,W). W\<in>n\<rightarrow>T}" by auto
  } thus "ProductTopBase(n,T) \<subseteq> {FinProd(n\<rightarrow>\<Union>T,W). W\<in>n\<rightarrow>T}" by auto
qed

text\<open>A technical lemma providing a formula for finite product on one topological space.\<close>

lemma single_top_prod: assumes A1: "W:1\<rightarrow>\<tau>" 
  shows "FinProd(1\<rightarrow>\<Union>\<tau>,W) = { {\<langle>0,y\<rangle>}. y \<in> W`(0)}"
proof -
  have "1 = {0}" by auto
  from A1 have "domain(W) = {0}" using func1_1_L1 by auto
  then have "FinProd(1\<rightarrow>\<Union>\<tau>,W) = {x \<in> 1\<rightarrow>\<Union>\<tau>. x`(0) \<in> W`(0)}"
    using FinProd_def by simp
  also have "{x \<in> 1\<rightarrow>\<Union>\<tau>. x`(0) \<in> W`(0)} = { {\<langle>0,y\<rangle>}. y \<in> W`(0)}"
  proof
    from \<open>1 = {0}\<close> show "{x \<in> 1\<rightarrow>\<Union>\<tau>. x`(0) \<in> W`(0)} \<subseteq> { {\<langle>0,y\<rangle>}. y \<in> W`(0)}"
      using func_singleton_pair by auto 
    { fix x assume "x \<in> { {\<langle>0,y\<rangle>}. y \<in> W`(0)}"
      then obtain y where "x = {\<langle>0,y\<rangle>}" and II: "y \<in> W`(0)" by auto
      with A1 have "y \<in> \<Union>\<tau>" using apply_funtype by auto
      with \<open>x = {\<langle>0,y\<rangle>}\<close>  \<open>1 = {0}\<close> have "x:1\<rightarrow>\<Union>\<tau>" using pair_func_singleton
        by auto
      with \<open>x = {\<langle>0,y\<rangle>}\<close> II have "x \<in> {x \<in> 1\<rightarrow>\<Union>\<tau>. x`(0) \<in> W`(0)}"
        using pair_val by simp
    } thus "{ {\<langle>0,y\<rangle>}. y \<in> W`(0)} \<subseteq> {x \<in> 1\<rightarrow>\<Union>\<tau>. x`(0) \<in> W`(0)}" by auto
  qed
  finally show ?thesis by simp 
qed

text\<open>Intuitively, the topological space of singleton lists valued in $X$ 
  is the same as $X$. However, each element of this space is a list of length one,
  i.e a set consisting of a pair $\langle 0, x\rangle$ where $x$ is an element of $X$.
  The next lemma provides a formula for the product topology in the corner case when we have 
  only one factor and shows that the product topology of one space is essentially the same as 
  the space.\<close>

lemma singleton_prod_top: assumes A1: "\<tau> {is a topology}" 
  shows 
    "SeqProductTopology(1,\<tau>) = { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}" and
    "IsAhomeomorphism(\<tau>,SeqProductTopology(1,\<tau>),{\<langle>y,{\<langle>0,y\<rangle>}\<rangle>.y \<in> \<Union>\<tau>})"
proof -
  have "{0} = 1" by auto
  let ?b = "{\<langle>y,{\<langle>0,y\<rangle>}\<rangle>.y \<in> \<Union>\<tau>}"
  have "?b \<in> bij(\<Union>\<tau>,1\<rightarrow>\<Union>\<tau>)" using list_singleton_bij by blast
  with A1 have "{?b``(U). U\<in>\<tau>} {is a topology}" and "IsAhomeomorphism(\<tau>, {?b``(U). U\<in>\<tau>},?b)"
    using bij_induced_top by auto
  moreover have "\<forall>U\<in>\<tau>. ?b``(U) = { {\<langle>0,y\<rangle>}. y\<in>U }"
  proof
    fix U assume "U\<in>\<tau>"
    from \<open>?b \<in> bij(\<Union>\<tau>,1\<rightarrow>\<Union>\<tau>)\<close> have "?b:\<Union>\<tau>\<rightarrow>(1\<rightarrow>\<Union>\<tau>)" using bij_def inj_def
      by simp
    { fix y assume "y \<in> \<Union>\<tau>"
      with \<open>?b:\<Union>\<tau>\<rightarrow>(1\<rightarrow>\<Union>\<tau>)\<close> have "?b`(y) = {\<langle>0,y\<rangle>}" using ZF_fun_from_tot_val
        by simp
    } hence "\<forall>y \<in> \<Union>\<tau>. ?b`(y) = {\<langle>0,y\<rangle>}" by auto
    with  \<open>U\<in>\<tau>\<close> \<open>?b:\<Union>\<tau>\<rightarrow>(1\<rightarrow>\<Union>\<tau>)\<close> show " ?b``(U) = { {\<langle>0,y\<rangle>}. y\<in>U }"
      using func_imagedef by auto 
  qed
  moreover have "ProductTopBase(1,\<tau>) = { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}"
  proof
    { fix V assume "V \<in> ProductTopBase(1,\<tau>)"
      with A1 obtain W where "W:1\<rightarrow>\<tau>" and "V = FinProd(1\<rightarrow>\<Union>\<tau>,W)"
        using fin_prod_def_nat by auto
      then have "V \<in> { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}" using apply_funtype single_top_prod
        by auto 
    } thus "ProductTopBase(1,\<tau>) \<subseteq> { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}" by auto
  { fix V assume "V \<in> { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}"
    then obtain U where "U\<in>\<tau>" and "V = { {\<langle>0,y\<rangle>}. y\<in>U }" by auto 
    let ?W = "{\<langle>0,U\<rangle>}"
    from \<open>U\<in>\<tau>\<close> have "?W:{0}\<rightarrow>\<tau>" using pair_func_singleton by simp   
    with \<open>{0} = 1\<close> have "?W:1\<rightarrow>\<tau>" and "?W`(0) = U" using pair_val by auto
    with \<open>V = { {\<langle>0,y\<rangle>}. y\<in>U }\<close> have "V = FinProd(1\<rightarrow>\<Union>\<tau>,?W)"
      using single_top_prod by simp 
    with A1 \<open>?W:1\<rightarrow>\<tau>\<close> have "V \<in> ProductTopBase(1,\<tau>)" using fin_prod_def_nat
      by auto
   } thus "{ { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>} \<subseteq> ProductTopBase(1,\<tau>)" by auto 
  qed
  ultimately have I: "ProductTopBase(1,\<tau>) {is a topology}" and 
    II: "IsAhomeomorphism(\<tau>, ProductTopBase(1,\<tau>),?b)" by auto
  from A1 have "ProductTopBase(1,\<tau>) {is a base for} SeqProductTopology(1,\<tau>)" 
    using seq_prod_top_is_top by simp
  with I have "ProductTopBase(1,\<tau>) = SeqProductTopology(1,\<tau>)" by (rule base_topology)
  with \<open>ProductTopBase(1,\<tau>) = { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}\<close> II show
    "SeqProductTopology(1,\<tau>) = { { {\<langle>0,y\<rangle>}. y\<in>U }. U\<in>\<tau>}" and
    "IsAhomeomorphism(\<tau>,SeqProductTopology(1,\<tau>),{\<langle>y,{\<langle>0,y\<rangle>}\<rangle>.y \<in> \<Union>\<tau>})" by auto
qed

text\<open>A special corner case of \<open>finite_top_prod_homeo\<close>: a space $X$ 
  is homeomorphic to the space of one element lists of $X$.\<close>

theorem singleton_prod_top1: assumes A1: "\<tau> {is a topology}" 
  shows "IsAhomeomorphism(SeqProductTopology(1,\<tau>),\<tau>,{\<langle>x,x`(0)\<rangle>. x\<in>1\<rightarrow>\<Union>\<tau>})"
proof -
  have "{\<langle>x,x`(0)\<rangle>. x\<in>1\<rightarrow>\<Union>\<tau>} = converse({\<langle>y,{\<langle>0,y\<rangle>}\<rangle>.y\<in>\<Union>\<tau>})" 
    using list_singleton_bij by blast
  with A1 show ?thesis using singleton_prod_top homeo_inv by simp
qed 
 
text\<open>A technical lemma describing the carrier of a (cartesian) product topology of  
the (sequence) product topology of $n$ copies of topology $\tau$ and another 
copy of $\tau$.\<close>

lemma finite_prod_top: assumes "\<tau> {is a topology}" and  "T = SeqProductTopology(n,\<tau>)"
  shows "(\<Union>ProductTopology(T,\<tau>)) = (n\<rightarrow>\<Union>\<tau>)\<times>\<Union>\<tau>"
  using assms Top_1_4_T1 seq_prod_top_is_top by simp

text\<open>If $U$ is a set from the base of $X^n$ and $V$ is open in $X$, then $U\times V$
is in the base of $X^{n+1}$. The next lemma is an analogue of this fact for the 
function space approach.\<close>

lemma finite_prod_succ_base: assumes A1: "\<tau> {is a topology}" and A2: "n \<in> nat" and 
  A3: "U \<in> ProductTopBase(n,\<tau>)" and A4: "V\<in>\<tau>"
  shows "{x \<in> succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> U \<and> x`(n) \<in> V} \<in> ProductTopBase(succ(n),\<tau>)"
  proof -
    let ?B = "{x \<in> succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> U \<and> x`(n) \<in> V}"
    from A1 A2 have "ProductTopBase(n,\<tau>) = {FinProd(n\<rightarrow>\<Union>\<tau>,W). W\<in>n\<rightarrow>\<tau>}"
      using fin_prod_def_nat by simp
    with A3 obtain W\<^sub>U where "W\<^sub>U:n\<rightarrow>\<tau>" and "U =FinProd(n\<rightarrow>\<Union>\<tau>,W\<^sub>U)" by auto
    let ?W = "Append(W\<^sub>U,V)"
    from A4 and \<open>W\<^sub>U:n\<rightarrow>\<tau>\<close> have "?W:succ(n)\<rightarrow>\<tau>" using append_props by simp
    moreover have "?B = FinProd(succ(n)\<rightarrow>\<Union>\<tau>,?W)"
    proof
      { fix x assume "x\<in>?B"
        with \<open>?W:succ(n)\<rightarrow>\<tau>\<close> have "x \<in> succ(n)\<rightarrow>\<Union>\<tau>" and "domain(?W) = succ(n)" using func1_1_L1 
          by auto
        moreover from A2 A4 \<open>x\<in>?B\<close> \<open>U =FinProd(n\<rightarrow>\<Union>\<tau>,W\<^sub>U)\<close> \<open>W\<^sub>U:n\<rightarrow>\<tau>\<close> \<open>x \<in> succ(n)\<rightarrow>\<Union>\<tau>\<close> 
        have "\<forall>i\<in>succ(n). x`(i) \<in> ?W`(i)" using func1_1_L1 FinProd_def init_props append_props
          by simp 
        ultimately have "x \<in> FinProd(succ(n)\<rightarrow>\<Union>\<tau>,?W)" using FinProd_def by simp 
      } thus "?B \<subseteq> FinProd(succ(n)\<rightarrow>\<Union>\<tau>,?W)" by auto
      next
      { fix x assume "x \<in> FinProd(succ(n)\<rightarrow>\<Union>\<tau>,?W)"
        then have "x:succ(n)\<rightarrow>\<Union>\<tau>" and I: "\<forall>i \<in> domain(?W). x`(i) \<in> ?W`(i)"
          using FinProd_def by auto
        moreover have "Init(x) \<in> U"
        proof -
          from A2 and \<open>x:succ(n)\<rightarrow>\<Union>\<tau>\<close> have "Init(x):n\<rightarrow>\<Union>\<tau>" using init_props by simp 
          moreover have "\<forall>i\<in>domain(W\<^sub>U). Init(x)`(i) \<in> W\<^sub>U`(i)"
          proof -
            from A2 \<open>x \<in> FinProd(succ(n)\<rightarrow>\<Union>\<tau>,?W)\<close> \<open>?W:succ(n)\<rightarrow>\<tau>\<close> have "\<forall>i\<in>n. x`(i) \<in> ?W`(i)"
              using FinProd_def func1_1_L1 by simp 
            moreover from A2 \<open>x: succ(n)\<rightarrow>\<Union>\<tau>\<close> have "\<forall>i\<in>n. Init(x)`(i) = x`(i)"
              using init_props by simp
            moreover from A4 and \<open>W\<^sub>U:n\<rightarrow>\<tau>\<close> have "\<forall>i\<in>n. ?W`(i) =  W\<^sub>U`(i)"
              using append_props by simp
            ultimately have "\<forall>i\<in>n. Init(x)`(i) \<in> W\<^sub>U`(i)" by simp
            with \<open>W\<^sub>U:n\<rightarrow>\<tau>\<close> show ?thesis using func1_1_L1 by simp 
          qed
          ultimately have "Init(x) \<in> FinProd(n\<rightarrow>\<Union>\<tau>,W\<^sub>U)" using FinProd_def by simp
          with \<open>U =FinProd(n\<rightarrow>\<Union>\<tau>,W\<^sub>U)\<close> show ?thesis by simp 
        qed
        moreover have "x`(n) \<in> V"       
        proof -  
          from \<open>?W:succ(n)\<rightarrow>\<tau>\<close> I  have "x`(n) \<in> ?W`(n)" using func1_1_L1 by simp
          moreover from A4 \<open>W\<^sub>U:n\<rightarrow>\<tau>\<close> have "?W`(n) = V" using append_props by simp
          ultimately show ?thesis by simp 
        qed
        ultimately have "x\<in>?B" by simp  
      } thus "FinProd(succ(n)\<rightarrow>\<Union>\<tau>,?W) \<subseteq> ?B" by auto
    qed
    moreover from A1 A2 have 
      "ProductTopBase(succ(n),\<tau>) = {FinProd(succ(n)\<rightarrow>\<Union>\<tau>,W). W\<in>succ(n)\<rightarrow>\<tau>}"
      using fin_prod_def_nat by simp
    ultimately show ?thesis by auto
 qed

text\<open>If $U$ is open in $X^n$ and $V$ is open in $X$, then $U\times V$ is open in $X^{n+1}$. 
The next lemma is an analogue of this fact for the function space approach.\<close>

lemma finite_prod_succ: assumes A1: "\<tau> {is a topology}" and A2: "n \<in> nat" and 
  A3: "U \<in> SeqProductTopology(n,\<tau>)" and A4: "V\<in>\<tau>"
  shows "{x \<in> succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> U \<and> x`(n) \<in> V} \<in> SeqProductTopology(succ(n),\<tau>)"
  proof -
     from A1 have "ProductTopBase(n,\<tau>) {is a base for} SeqProductTopology(n,\<tau>)" and 
      I: "ProductTopBase(succ(n),\<tau>) {is a base for} SeqProductTopology(succ(n),\<tau>)" and 
      II: "SeqProductTopology(succ(n),\<tau>) {is a topology}"
        using seq_prod_top_is_top by auto
    with A3 have "\<exists>\<B> \<in> Pow(ProductTopBase(n,\<tau>)). U = \<Union>\<B>" using Top_1_2_L1 by simp
    then obtain \<B> where "\<B> \<subseteq> ProductTopBase(n,\<tau>)" and "U = \<Union>\<B>" by auto
    then have 
    "{x:succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> U \<and> x`(n) \<in> V} = (\<Union>B\<in>\<B>.{x:succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> B \<and> x`(n) \<in> V})"
      by auto
    moreover from A1 A2 A4 \<open>\<B> \<subseteq> ProductTopBase(n,\<tau>)\<close> have
      "\<forall>B\<in>\<B>. ({x:succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> B \<and> x`(n) \<in> V} \<in> ProductTopBase(succ(n),\<tau>))"
      using finite_prod_succ_base by auto
    with I II have 
      "(\<Union>B\<in>\<B>.{x:succ(n)\<rightarrow>\<Union>\<tau>. Init(x) \<in> B \<and> x`(n) \<in> V}) \<in> SeqProductTopology(succ(n),\<tau>)"
      using base_sets_open union_indexed_open by auto
    ultimately show ?thesis by simp
  qed

    
text\<open>In the \<open>Topology_ZF_2\<close> theory we define product topology of two topological spaces.
The next lemma explains in what sense the topology on finite lists of length $n$ of 
elements of topological space $X$ can be thought as a model of the product topology on the cartesian 
product of $n$ copies of that space. Namely, we show that the space of lists of length $n+1$ 
of elements of $X$  is homeomorphic to the product topology (as defined in \<open>Topology_ZF_2\<close>) 
of two spaces: the space of lists of length $n$ and $X$. Recall that if $\mathcal{B}$ is a base 
(i.e. satisfies the base condition), then the collection $\{\bigcup B| B \in Pow(\mathcal{B})\}$ 
is a topology (generated by $\mathcal{B}$).\<close>

theorem finite_top_prod_homeo: assumes A1: "\<tau> {is a topology}" and A2: "n \<in> nat" and 
  A3: "f = {\<langle>x,\<langle>Init(x),x`(n)\<rangle>\<rangle>. x \<in> succ(n)\<rightarrow>\<Union>\<tau>}" and
  A4: "T = SeqProductTopology(n,\<tau>)" and
  A5: "S = SeqProductTopology(succ(n),\<tau>)"
shows "IsAhomeomorphism(S,ProductTopology(T,\<tau>),f)"
proof -
  let ?C = "ProductCollection(T,\<tau>)"
  let ?B = "ProductTopBase(succ(n),\<tau>)"
  from A1 A4 have "T {is a topology}" using seq_prod_top_is_top by simp
  with A1 A5  have "S {is a topology}" and " ProductTopology(T,\<tau>) {is a topology}" 
        using seq_prod_top_is_top  Top_1_4_T1 by auto
  moreover 
  from assms have "f \<in> bij(\<Union>S,\<Union>ProductTopology(T,\<tau>))"
    using lists_cart_prod seq_prod_top_is_top Top_1_4_T1 by simp
  then have "f: \<Union>S\<rightarrow>\<Union>ProductTopology(T,\<tau>)" using bij_is_fun by simp
  ultimately have "two_top_spaces0(S,ProductTopology(T,\<tau>),f)" using two_top_spaces0_def by simp
  moreover note \<open>f \<in> bij(\<Union>S,\<Union>ProductTopology(T,\<tau>))\<close>
  moreover from A1 A5 have "?B {is a base for} S"
    using seq_prod_top_is_top by simp
  moreover from A1 \<open>T {is a topology}\<close> have "?C {is a base for} ProductTopology(T,\<tau>)" 
    using Top_1_4_T1 by auto
  moreover have  "\<forall>W\<in>?C. f-``(W) \<in> S"
  proof
      fix W assume "W\<in>?C"
      then obtain U V where "U\<in>T" "V\<in>\<tau>" and "W = U\<times>V" using ProductCollection_def by auto  
      from A1 A5 \<open>f: \<Union>S\<rightarrow>\<Union>ProductTopology(T,\<tau>)\<close> have "f: (succ(n)\<rightarrow>\<Union>\<tau>)\<rightarrow>\<Union>ProductTopology(T,\<tau>)"
        using seq_prod_top_is_top by simp
      with assms \<open>W = U\<times>V\<close> \<open>U\<in>T\<close> \<open>V\<in>\<tau>\<close> show "f-``(W) \<in> S" 
        using ZF_fun_from_tot_val func1_1_L15 finite_prod_succ by simp 
  qed
  moreover have "\<forall>V\<in>?B. f``(V) \<in> ProductTopology(T,\<tau>)"
  proof
    fix V assume "V\<in>?B"
    with A1 A2 obtain W\<^sub>V where "W\<^sub>V \<in> succ(n)\<rightarrow>\<tau>" and "V = FinProd(succ(n)\<rightarrow>\<Union>\<tau>,W\<^sub>V)" 
      using fin_prod_def_nat by auto
    let ?U = "FinProd(n\<rightarrow>\<Union>\<tau>,Init(W\<^sub>V))"
    let ?W = "W\<^sub>V`(n)"
    have "?U \<in> T"
    proof - 
      from A1 A2 \<open>W\<^sub>V \<in> succ(n)\<rightarrow>\<tau>\<close> have "?U \<in> ProductTopBase(n,\<tau>)" 
        using fin_prod_def_nat init_props by auto
      with A1 A4 show ?thesis using seq_prod_top_is_top base_sets_open by blast
    qed
    from A1 \<open>W\<^sub>V \<in> succ(n)\<rightarrow>\<tau>\<close> \<open>T {is a topology}\<close> \<open>?U \<in> T\<close> have "?U\<times>?W \<in> ProductTopology(T,\<tau>)"
      using apply_funtype prod_open_open_prod by simp
    moreover have "f``(V) = ?U\<times>?W"
    proof -
      from A2 \<open>W\<^sub>V: succ(n)\<rightarrow>\<tau>\<close> have "Init(W\<^sub>V): n\<rightarrow>\<tau>" and III: "\<forall>k\<in>n. Init(W\<^sub>V)`(k) = W\<^sub>V`(k)" 
        using init_props by auto
      then have "domain(Init(W\<^sub>V)) = n" using func1_1_L1 by simp
      have "f``(V) = {\<langle>Init(x),x`(n)\<rangle>. x\<in>V}"
      proof -
        have "f``(V) = {f`(x). x\<in>V}"
        proof -
          from A1 A5 have "?B {is a base for} S" using seq_prod_top_is_top by simp 
          with \<open>V\<in>?B\<close> have "V \<subseteq> \<Union>S" using IsAbaseFor_def by auto
          with \<open>f: \<Union>S\<rightarrow>\<Union>ProductTopology(T,\<tau>)\<close> show ?thesis using func_imagedef by simp
        qed
        moreover have "\<forall>x\<in>V. f`(x) = \<langle>Init(x),x`(n)\<rangle>"
        proof -
          from A1 A3 A5 \<open>V = FinProd(succ(n)\<rightarrow>\<Union>\<tau>,W\<^sub>V)\<close> have "V \<subseteq> \<Union>S" and 
            fdef: "f = {\<langle>x,\<langle>Init(x),x`(n)\<rangle>\<rangle>. x \<in> \<Union>S}" using seq_prod_top_is_top FinProd_def 
            by auto 
          from \<open>f: \<Union>S\<rightarrow>\<Union>ProductTopology(T,\<tau>)\<close> fdef have "\<forall>x \<in> \<Union>S. f`(x) = \<langle>Init(x),x`(n)\<rangle>" 
            by (rule ZF_fun_from_tot_val0)  
          with \<open>V \<subseteq> \<Union>S\<close> show ?thesis by auto  
        qed
        ultimately show ?thesis by simp 
      qed
      also have "{\<langle>Init(x),x`(n)\<rangle>. x\<in>V} = ?U\<times>?W"
      proof
        { fix y assume "y \<in> {\<langle>Init(x),x`(n)\<rangle>. x\<in>V}"
          then obtain x where I: "y = \<langle>Init(x),x`(n)\<rangle>" and "x\<in>V" by auto 
          with \<open>V = FinProd(succ(n)\<rightarrow>\<Union>\<tau>,W\<^sub>V)\<close> have 
            "x:succ(n)\<rightarrow>\<Union>\<tau>" and II: "\<forall>k\<in>domain(W\<^sub>V). x`(k) \<in> W\<^sub>V`(k)" 
            unfolding FinProd_def by auto
          with A2 \<open>W\<^sub>V: succ(n)\<rightarrow>\<tau>\<close> have IV: "\<forall>k\<in>n. Init(x)`(k) = x`(k)" 
            using init_props by simp 
          have "Init(x) \<in> ?U"
          proof -
            from A2 \<open>x:succ(n)\<rightarrow>\<Union>\<tau>\<close> have "Init(x): n\<rightarrow>\<Union>\<tau>" using init_props by simp 
            moreover have "\<forall>k\<in>domain(Init(W\<^sub>V)). Init(x)`(k) \<in> Init(W\<^sub>V)`(k)"
            proof -
              from A2 \<open>W\<^sub>V: succ(n)\<rightarrow>\<tau>\<close> have "Init(W\<^sub>V): n\<rightarrow>\<tau>" using init_props by simp
              then have "domain(Init(W\<^sub>V)) = n" using func1_1_L1 by simp
              note III IV  \<open>domain(Init(W\<^sub>V)) = n\<close>
              moreover from II \<open>W\<^sub>V \<in> succ(n)\<rightarrow>\<tau>\<close> have "\<forall>k\<in>n. x`(k) \<in> W\<^sub>V`(k)" 
                using func1_1_L1 by simp
              ultimately show ?thesis by simp 
            qed
            ultimately show "Init(x) \<in> ?U" using FinProd_def by simp
          qed
          moreover from \<open>W\<^sub>V: succ(n)\<rightarrow>\<tau>\<close> II have "x`(n) \<in> ?W" using func1_1_L1 by simp
          ultimately have "\<langle>Init(x),x`(n)\<rangle> \<in> ?U\<times>?W" by simp 
          with I have "y \<in> ?U\<times>?W" by simp 
        } thus "{\<langle>Init(x),x`(n)\<rangle>. x\<in>V} \<subseteq> ?U\<times>?W" by auto
        { fix y assume "y \<in> ?U\<times>?W"
          then have "fst(y) \<in> ?U" and "snd(y) \<in> ?W" by auto
          with \<open>domain(Init(W\<^sub>V)) = n\<close> have "fst(y): n\<rightarrow>\<Union>\<tau>" and 
            V: "\<forall>k\<in>n. fst(y)`(k) \<in> Init(W\<^sub>V)`(k)"
            using FinProd_def by auto
          from \<open>W\<^sub>V: succ(n)\<rightarrow>\<tau>\<close> have "?W \<in> \<tau>" using apply_funtype by simp
          with \<open>snd(y) \<in> ?W\<close> have "snd(y) \<in> \<Union>\<tau>" by auto     
          let ?x = "Append(fst(y),snd(y))"
          have "?x\<in>V"
          proof -
            from \<open>fst(y): n\<rightarrow>\<Union>\<tau>\<close> \<open>snd(y) \<in> \<Union>\<tau>\<close> have "?x:succ(n)\<rightarrow>\<Union>\<tau>" using append_props by simp
            moreover have "\<forall>i\<in>domain(W\<^sub>V). ?x`(i) \<in> W\<^sub>V`(i)"             
            proof -
              from \<open>fst(y): n\<rightarrow>\<Union>\<tau>\<close> \<open>snd(y) \<in> \<Union>\<tau>\<close> 
                have "\<forall>k\<in>n. ?x`(k) = fst(y)`(k)" and "?x`(n) = snd(y)" 
                using append_props by auto
              moreover from III V have "\<forall>k\<in>n. fst(y)`(k) \<in> W\<^sub>V`(k)" by simp 
              moreover note \<open>snd(y) \<in> ?W\<close>
              ultimately have "\<forall>i\<in>succ(n). ?x`(i) \<in> W\<^sub>V`(i)" by simp
              with \<open>W\<^sub>V \<in> succ(n)\<rightarrow>\<tau>\<close> show ?thesis using func1_1_L1 by simp 
            qed
            ultimately have "?x \<in> FinProd(succ(n)\<rightarrow>\<Union>\<tau>,W\<^sub>V)" using FinProd_def by simp
            with \<open>V = FinProd(succ(n)\<rightarrow>\<Union>\<tau>,W\<^sub>V)\<close> show "?x\<in>V" by simp  
          qed
          moreover from A2 \<open>y \<in> ?U\<times>?W\<close> \<open>fst(y): n\<rightarrow>\<Union>\<tau>\<close> \<open>snd(y) \<in> \<Union>\<tau>\<close> have "y = \<langle>Init(?x),?x`(n)\<rangle>"
            using init_append append_props by auto  
          ultimately have "y \<in> {\<langle>Init(x),x`(n)\<rangle>. x\<in>V}" by auto 
        } thus "?U\<times>?W \<subseteq> {\<langle>Init(x),x`(n)\<rangle>. x\<in>V}" by auto
      qed
      finally show "f``(V) = ?U\<times>?W" by simp 
    qed
    ultimately show "f``(V) \<in> ProductTopology(T,\<tau>)" by simp 
  qed
  ultimately show ?thesis using two_top_spaces0.bij_base_open_homeo by simp 
qed
   

end
