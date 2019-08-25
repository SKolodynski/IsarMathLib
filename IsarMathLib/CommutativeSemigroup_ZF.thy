(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2007-2009  Slawomir Kolodynski

    This progr\rightarowam is free software; Redistribution and use in source and binary forms, 
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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)


section \<open>Commutative Semigroups\<close>

theory CommutativeSemigroup_ZF imports Semigroup_ZF

begin

text\<open>In the \<open>Semigroup\<close> theory we introduced a notion 
  of \<open>SetFold(f,a,\<Lambda>,r)\<close> that represents the sum of 
  values of some function $a$ valued in a semigroup
  where the arguments of that function vary over some set $\Lambda$.
  Using the additive notation something like this would be expressed
  as $\sum_{x\in \Lambda} f(x)$ in informal mathematics. 
  This theory considers an alternative to that notion that is more specific 
  to commutative semigroups.
\<close>

subsection\<open>Sum of a function over a set\<close>

text\<open>The $r$ parameter in the definition of \<open>SetFold(f,a,\<Lambda>,r)\<close>
  (from \<open>Semigroup_ZF\<close>) represents a linear order relation 
  on $\Lambda$ that is needed to indicate in what order we are summing 
  the values $f(x)$.
  If the semigroup operation is commutative the order does not matter
  and the relation $r$ is not needed. In this section we define a notion 
  of summing up values of some function $a : X \rightarrow G$
  over a finite set of indices $\Gamma \subseteq X$, without using any
  order relation on $X$.\<close>


text\<open>We define the sum of values of a function $a: X\rightarrow G$
  over a set $\Lambda$ as the only element of the set of sums of lists 
  that are bijections between the number of values in $\Lambda$ 
  (which is a natural number $n = \{0,1, .. , n-1\}$ if $\Lambda$
  is finite) and $\Lambda$. The notion of \<open>Fold1(f,c)\<close> 
  is defined in \<open>Semigroup_ZF\<close> as the fold (sum) of the list
  $c$ starting from the first element of that list. The intention
  is to use the fact that since the result of summing up a list
  does not depend on the order, the set 
  \<open>{Fold1(f,a O b). b \<in> bij( |\<Lambda>|, \<Lambda>)}\<close> is a singleton
  and we can extract its only value by taking its union.\<close>

definition
  "CommSetFold(f,a,\<Lambda>) = \<Union>{Fold1(f,a O b). b \<in> bij(|\<Lambda>|, \<Lambda>)}"

text\<open>the next locale sets up notation for writing about summation in
  commutative semigroups. We define two kinds of sums. One is the sum
  of elements of a list (which are just functions defined on a natural number)
  and the second one represents a more general notion the sum of values of
  a semigroup valued function over some set of arguments. Since those two types of 
  sums are different notions they are represented by different symbols.
  However in the presentations they are both intended to be printed as $\sum $.\<close>

locale commsemigr =
  
  fixes G f

  assumes csgassoc: "f {is associative on} G"

  assumes csgcomm: "f {is commutative on} G"

  fixes csgsum (infixl "\<ra>" 69)
  defines csgsum_def[simp]: "x \<ra> y \<equiv> f`\<langle>x,y\<rangle>"

  fixes X a
  assumes csgaisfun: "a : X \<rightarrow> G"

  fixes csglistsum ("\<Sum> _" 70)
  defines csglistsum_def[simp]: "\<Sum>k \<equiv> Fold1(f,k)"

  fixes csgsetsum ("\<ssum>")
  defines csgsetsum_def[simp]: "\<ssum>(A,h) \<equiv> CommSetFold(f,h,A)"


text\<open>Definition of a sum of function over a set in 
  notation defined in the \<open>commsemigr\<close> locale.\<close>

lemma (in commsemigr) CommSetFolddef: 
  shows "(\<ssum>(A,a)) = (\<Union>{\<Sum>(a O b). b \<in> bij(|A|, A)})"
  using CommSetFold_def by simp

text\<open>The next lemma states that the result of a sum does not depend
  on the order we calculate it. This is similar to lemma 
  \<open>prod_order_irr\<close> in the \<open>Semigroup\<close> theory,
  except that the \<open>semigr1\<close> locale assumes
  that the domain of the function we sum up is linearly
  ordered, while in \<open>commsemigr\<close> we don't have
  this assumption.\<close>

lemma (in commsemigr) sum_over_set_bij: 
  assumes A1: "A \<in> FinPow(X)" "A \<noteq> 0" and A2: "b \<in> bij(|A|,A)" 
  shows "(\<ssum>(A,a)) = (\<Sum> (a O b))"
proof -
  have 
    "\<forall>c \<in> bij(|A|,A). \<forall> d \<in> bij(|A|,A). (\<Sum>(a O c)) = (\<Sum>(a O d))"
  proof -
    { fix c assume "c \<in> bij(|A|,A)"
      fix d assume "d \<in> bij(|A|,A)"
      let ?r = "InducedRelation(converse(c), Le)"
      have "semigr1(G,f,A,?r,restrict(a, A))"
      proof -
	have "semigr0(G,f)" using csgassoc semigr0_def by simp
	moreover from A1 \<open>c \<in> bij(|A|,A)\<close> have "IsLinOrder(A,?r)" 
	  using bij_converse_bij card_fin_is_nat 
            natord_lin_on_each_nat ind_rel_pres_lin by simp
	moreover from A1 have "restrict(a, A) : A \<rightarrow> G"
	  using FinPow_def csgaisfun restrict_fun by simp
	ultimately show ?thesis using semigr1_axioms.intro semigr1_def 
	  by simp
      qed
      moreover have "f {is commutative on} G" using csgcomm
	by simp
      moreover from A1 have "A \<in>  FinPow(A)" "A \<noteq> 0"
	using FinPow_def by auto
      moreover note \<open>c \<in> bij(|A|,A)\<close> \<open>d \<in> bij(|A|,A)\<close>
      ultimately have 
	"Fold1(f,restrict(a,A) O c) = Fold1(f,restrict(a,A) O d)"
	by (rule semigr1.prod_bij_same)
      hence "(\<Sum> (restrict(a,A) O c)) = (\<Sum> (restrict(a,A) O d))"
	by simp
      moreover from A1 \<open>c \<in> bij(|A|,A)\<close> \<open>d \<in> bij(|A|,A)\<close>
      have 
	"restrict(a,A) O c = a O c" and "restrict(a,A) O d = a O d"
	using bij_def surj_def csgaisfun FinPow_def comp_restrict
	by auto
      ultimately have "(\<Sum>(a O c)) = (\<Sum>(a O d))" by simp
      } thus ?thesis by blast
    qed
  with A2 have "(\<Union>{\<Sum>(a O b). b \<in> bij(|A|, A)}) = (\<Sum> (a O b))"
    by (rule singleton_comprehension)
  then show ?thesis using CommSetFolddef by simp
qed

text\<open>The result of a sum is in the semigroup. Also, as the second
  assertion we show that every semigroup valued function
  generates a homomorphism between the finite subsets of a semigroup 
  and the semigroup. Adding an element to a set coresponds to adding a 
  value.\<close>

lemma (in commsemigr) sum_over_set_add_point: 
  assumes  A1: "A \<in> FinPow(X)"  "A \<noteq> 0" 
  shows "\<ssum>(A,a) \<in> G" and
  "\<forall>x \<in> X-A. \<ssum>(A \<union> {x},a) = (\<ssum>(A,a)) \<ra> a`(x)"
proof -
  from A1 obtain b where "b \<in> bij(|A|,A)"
    using fin_bij_card by auto
  with A1 have "\<ssum>(A,a) = (\<Sum> (a O b))"
    using sum_over_set_bij by simp
  from A1 have "|A| \<in> nat" using card_fin_is_nat by simp
  have "semigr0(G,f)" using csgassoc semigr0_def by simp
  moreover
  from A1 obtain n where "n \<in> nat" and "|A| = succ(n)"
    using card_non_empty_succ by auto
  with A1  \<open>b \<in> bij(|A|,A)\<close> have 
    "n \<in> nat" and "a O b : succ(n) \<rightarrow> G"
    using bij_def inj_def FinPow_def comp_fun_subset csgaisfun 
    by auto
  ultimately have "Fold1(f,a O b) \<in> G" by (rule semigr0.prod_type)
  with \<open>\<ssum>(A,a) = (\<Sum> (a O b))\<close> show "\<ssum>(A,a) \<in> G"
    by simp
  { fix x assume "x \<in> X-A"
    with A1 have "(A \<union> {x}) \<in> FinPow(X)" and "A \<union> {x} \<noteq> 0"
      using singleton_in_finpow union_finpow by auto
    moreover have "Append(b,x) \<in> bij(|A \<union> {x}|, A \<union> {x})"
    proof -
      note \<open>|A| \<in> nat\<close> \<open>b \<in> bij(|A|,A)\<close>
      moreover from \<open>x \<in> X-A\<close> have "x \<notin> A" by simp
      ultimately have "Append(b,x) \<in> bij(succ(|A|), A \<union> {x})"
	by (rule bij_append_point)
      with A1 \<open>x \<in> X-A\<close> show ?thesis
	using card_fin_add_one by auto
    qed
    ultimately have "(\<ssum>(A \<union> {x},a)) =  (\<Sum> (a O Append(b,x)))"
      using sum_over_set_bij by simp
    also have "\<dots> = (\<Sum> Append(a O b, a`(x)))"
    proof -
      note \<open>|A| \<in> nat\<close>
      moreover 
      from A1 \<open>b \<in> bij(|A|, A)\<close> have 
	"b : |A| \<rightarrow> A" and "A \<subseteq> X"
	using bij_def inj_def using FinPow_def by auto
      then have "b : |A| \<rightarrow> X" by (rule func1_1_L1B)
      moreover from \<open>x \<in> X-A\<close> have "x \<in> X" and "a : X \<rightarrow> G"
	using csgaisfun by auto
      ultimately show ?thesis using list_compose_append
	by simp
    qed
    also have "\<dots> =  (\<ssum>(A,a)) \<ra> a`(x)" 
    proof -
      note \<open>semigr0(G,f)\<close>  \<open>n \<in> nat\<close>  \<open>a O b : succ(n) \<rightarrow> G\<close>
      moreover from \<open>x \<in> X-A\<close> have "a`(x) \<in> G"
	using csgaisfun apply_funtype by simp
      ultimately have 
	"Fold1(f,Append(a O b, a`(x))) = f`\<langle>Fold1(f,a O b),a`(x)\<rangle>"
	by (rule semigr0.prod_append)
      with A1 \<open>b \<in> bij(|A|,A)\<close> show ?thesis
	using sum_over_set_bij by simp
    qed
    finally have "(\<ssum>(A \<union> {x},a)) = (\<ssum>(A,a)) \<ra> a`(x)"
      by simp
  } thus "\<forall>x \<in> X-A. \<ssum>(A \<union> {x},a) = (\<ssum>(A,a)) \<ra> a`(x)"
    by simp
qed  

end