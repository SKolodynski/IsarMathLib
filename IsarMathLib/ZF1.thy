(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2005-2023  Slawomir Kolodynski

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

section \<open>ZF set theory basics\<close>

theory ZF1 imports ZF.Perm

begin

text\<open>The standard Isabelle distribution contains lots of facts about basic set
  theory. This theory file adds some more.\<close>

subsection\<open>Lemmas in Zermelo-Fraenkel set theory\<close>

text\<open>Here we put lemmas from the set theory that we could not find in 
  the standard Isabelle distribution or just so that they are easier to find.\<close>

text\<open>In Isabelle/ZF the set difference is written with a minus sign $A-B$
  because the standard backslash character is reserved for other purposes. 
  The next abbreviation declares that we want the set difference character $A\setminus B$
  to be synonymous with the minus sign. \<close>

abbreviation set_difference (infixl "\<setminus>" 65) where "A\<setminus>B \<equiv> A-B"

text\<open>Complement of the complement is the set.\<close>

lemma diff_diff_eq: assumes "A\<subseteq>X" shows "X\<setminus>(X\<setminus>A) = A" using assms by auto

text\<open>A set cannot be a member of itself. This is exactly lemma \<open>mem_not_refl\<close>
  from Isabelle/ZF \<open>upair.thy\<close>, we put it here for easy reference. \<close>

lemma mem_self: shows "x\<notin>x" by (rule mem_not_refl)

text\<open>If one collection is contained in another, then we can say the same
  about their unions.\<close>

lemma collection_contain: assumes "A\<subseteq>B" shows "\<Union>A \<subseteq> \<Union>B"
proof
  fix x assume "x \<in> \<Union>A"
  then obtain X where "x\<in>X" and "X\<in>A" by auto
  with assms show "x \<in> \<Union>B" by auto
qed

text\<open>In ZF set theory the zero of natural numbers is the same as the empty set.
  In the next abbreviation we declare that we want $0$ and $\emptyset$ to be synonyms
  so that we can use $\emptyset$ instead of $0$ when appropriate. \<close>

abbreviation empty_set ("\<emptyset>") where "\<emptyset> \<equiv> 0" 

text\<open>If all sets of a nonempty collection are the same, then its union 
  is the same.\<close>

lemma ZF1_1_L1: assumes "C\<noteq>\<emptyset>" and "\<forall>y\<in>C. b(y) = A" 
  shows "(\<Union>y\<in>C. b(y)) = A" using assms by blast
  
text\<open>The union af all values of a constant meta-function belongs to 
the same set as the constant.\<close>

lemma ZF1_1_L2: assumes A1:"C\<noteq>\<emptyset>" and A2: "\<forall>x\<in>C. b(x) \<in> A" 
  and A3: "\<forall>x y. x\<in>C \<and> y\<in>C \<longrightarrow> b(x) = b(y)"
  shows "(\<Union>x\<in>C. b(x))\<in>A"
proof -
  from A1 obtain x where D1: "x\<in>C" by auto
  with A3 have "\<forall>y\<in>C. b(y) = b(x)" by blast
  with A1 have "(\<Union>y\<in>C. b(y)) = b(x)" 
    using ZF1_1_L1 by simp
  with D1 A2 show ?thesis by simp
qed

text\<open>If two meta-functions are the same on a cartesian product,
  then the subsets defined by them are the same. I am surprised Isabelle
  can not handle this automatically.\<close>

lemma ZF1_1_L4: assumes A1: "\<forall>x\<in>X.\<forall>y\<in>Y. a(x,y) = b(x,y)"
  shows "{a(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y} = {b(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y}"
proof
  show "{a(x, y). \<langle>x,y\<rangle> \<in> X \<times> Y} \<subseteq> {b(x, y). \<langle>x,y\<rangle> \<in> X \<times> Y}"
  proof
    fix z assume "z \<in> {a(x, y) . \<langle>x,y\<rangle> \<in> X \<times> Y}"
    with A1 show  "z \<in> {b(x,y).\<langle>x,y\<rangle> \<in> X\<times>Y}" by auto   
  qed
  show "{b(x, y). \<langle>x,y\<rangle> \<in> X \<times> Y} \<subseteq> {a(x, y). \<langle>x,y\<rangle> \<in> X \<times> Y}"
  proof
    fix z assume "z \<in> {b(x, y). \<langle>x,y\<rangle> \<in> X \<times> Y}"
    with A1 show "z \<in> {a(x,y).\<langle>x,y\<rangle> \<in> X\<times>Y}" by auto
  qed
qed

text\<open>If two meta-functions are the same on a cartesian product,
  then the subsets defined by them are the same. 
  This is similar to \<open>ZF1_1_L4\<close>, except that
  the set definition varies over \<open>p\<in>X\<times>Y\<close> rather than 
  \<open>\<langle> x,y\<rangle>\<in>X\<times>Y\<close>.\<close>

lemma ZF1_1_L4A: assumes A1: "\<forall>x\<in>X.\<forall>y\<in>Y. a(\<langle> x,y\<rangle>) = b(x,y)"
  shows "{a(p). p \<in> X\<times>Y} = {b(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y}"
proof
  { fix z assume "z \<in> {a(p). p\<in>X\<times>Y}"
    then obtain p where D1: "z=a(p)" "p\<in>X\<times>Y" by auto
    let ?x = "fst(p)" let ?y = "snd(p)"
    from A1 D1 have "z \<in> {b(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y}" by auto
  } then show "{a(p). p \<in> X\<times>Y} \<subseteq> {b(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y}" by blast
next 
  { fix z assume "z \<in> {b(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y}"
    then obtain x y where D1: "\<langle>x,y\<rangle> \<in> X\<times>Y" "z=b(x,y)" by auto
    let ?p = "\<langle> x,y\<rangle>" 
    from A1 D1 have "?p\<in>X\<times>Y" "z = a(?p)" by auto
    then have "z \<in> {a(p). p \<in> X\<times>Y}" by auto
  } then show "{b(x,y). \<langle>x,y\<rangle> \<in> X\<times>Y} \<subseteq> {a(p). p \<in> X\<times>Y}" by blast
qed

text\<open>A lemma about inclusion in cartesian products. Included here to remember
  that we need the $U\times V \neq \emptyset$ assumption.\<close>

lemma prod_subset: assumes "U\<times>V\<noteq>\<emptyset>" "U\<times>V \<subseteq> X\<times>Y" shows "U\<subseteq>X" and "V\<subseteq>Y"
  using assms by auto

text\<open>A technical lemma about sections in cartesian products.\<close>

lemma section_proj: assumes "A \<subseteq> X\<times>Y" and "U\<times>V \<subseteq> A" and "x \<in> U"  "y \<in> V"
  shows "U \<subseteq> {t\<in>X. \<langle>t,y\<rangle> \<in> A}" and "V \<subseteq> {t\<in>Y. \<langle>x,t\<rangle> \<in> A}"
  using assms by auto

text\<open>If two meta-functions are the same on a set, then they define the same
  set by separation.\<close>

lemma ZF1_1_L4B: assumes "\<forall>x\<in>X. a(x) = b(x)"
  shows "{a(x). x\<in>X} = {b(x). x\<in>X}"
  using assms by simp

text\<open>A set defined by a constant meta-function is a singleton.\<close>

lemma ZF1_1_L5: assumes "X\<noteq>\<emptyset>" and "\<forall>x\<in>X. b(x) = c"
  shows "{b(x). x\<in>X} = {c}" using assms by blast

text\<open>Most of the time, \<open>auto\<close> does this job, but there are strange 
  cases when the next lemma is needed.\<close>

lemma subset_with_property: assumes "Y = {x\<in>X. b(x)}"
  shows "Y \<subseteq> X" 
  using assms by auto

text\<open>If set $A$ is contained in set $B$ and exist elements $x,y$ of the set $A$ 
  that satisfy a predicate then exist elements of the set $B$ that satisfy the predicate. \<close>

lemma exist2_subset: assumes "A\<subseteq>B" and "\<exists>x\<in>A. \<exists>y\<in>A. \<phi>(x,y)"
  shows "\<exists>x\<in>B. \<exists>y\<in>B. \<phi>(x,y)"
  using assms by blast

text\<open>We can choose an element from a nonempty set.\<close>

lemma nonempty_has_element: assumes "X\<noteq>\<emptyset>" shows "\<exists>x. x\<in>X"
  using assms by auto

(*text{*If after removing an element from a set we get an empty set,
  then this set must be a singleton.*}

lemma rem_point_empty: assumes "a\<in>A" and "A-{a} = \<emptyset>"
  shows "A = {a}" using assms by auto; *)

text\<open>In Isabelle/ZF the intersection of an empty family is 
  empty. This is exactly lemma \<open>Inter_0\<close> from Isabelle's
  \<open>equalities\<close> theory. We repeat this lemma here as it is very
  difficult to find. This is one reason we need comments before every 
  theorem: so that we can search for keywords.\<close>

lemma inter_empty_empty: shows "\<Inter>\<emptyset> = \<emptyset>" by (rule Inter_0)

text\<open>If an intersection of a collection is not empty, then the collection is
  not empty. We are (ab)using the fact the the intersection of empty collection 
  is defined to be empty.\<close>

lemma inter_nempty_nempty: assumes "\<Inter>A \<noteq> \<emptyset>" shows "A\<noteq>\<emptyset>"
  using assms by auto

text\<open>For two collections $S,T$ of sets we define the product collection
  as the collections of cartesian products $A\times B$, where $A\in S, B\in T$.\<close>

definition
  "ProductCollection(T,S) \<equiv> \<Union>U\<in>T.{U\<times>V. V\<in>S}"

text\<open>The union of the product collection of collections $S,T$ is the 
  cartesian product of $\bigcup S$ and  $\bigcup T$.\<close>

lemma ZF1_1_L6: shows "\<Union> ProductCollection(S,T) = \<Union>S \<times> \<Union>T"
  using ProductCollection_def by auto

text\<open>An intersection of subsets is a subset.\<close>

lemma ZF1_1_L7: assumes A1: "I\<noteq>\<emptyset>" and A2: "\<forall>i\<in>I. P(i) \<subseteq> X"
  shows "( \<Inter>i\<in>I. P(i) ) \<subseteq> X"
proof -
  from A1 obtain i\<^sub>0 where "i\<^sub>0 \<in> I" by auto
  with A2 have "( \<Inter>i\<in>I. P(i) ) \<subseteq> P(i\<^sub>0)" and "P(i\<^sub>0) \<subseteq> X"
    by auto
  thus "( \<Inter>i\<in>I. P(i) ) \<subseteq> X" by auto
qed

text\<open>A stronger version of \<open>ZF1_1_L7\<close> without the assumption
  that the collection of subsets is nonempty.\<close>

lemma inter_subsets_subset: assumes "\<forall>i\<in>I. P(i) \<subseteq> X"
  shows "(\<Inter>i\<in>I. P(i)) \<subseteq> X"
proof -
  { assume "I=\<emptyset>" 
    hence "(\<Inter>i\<in>I. P(i)) = \<emptyset>" by auto
    hence ?thesis by simp
  }
  with assms show ?thesis using ZF1_1_L7 by blast
qed

text\<open>Intersection of a smaller (but nonempty) collection of sets is larger.
  Note the assumption that the smaller collection is nonepty in necessary here.\<close>

lemma inter_index_mono: assumes "I\<subseteq>M" "I\<noteq>\<emptyset>"
  shows "(\<Inter>i\<in>M. P(i)) \<subseteq> (\<Inter>i\<in>I. P(i))"
  using assms by auto

text\<open>Isabelle/ZF has a "THE" construct that allows to define an element
  if there is only one such that is satisfies given predicate.
  In pure ZF we can express something similar using the indentity proven below.\<close>

lemma ZF1_1_L8: shows "\<Union>{x} = x" by auto

text\<open>Some properties of singletons.\<close>

lemma ZF1_1_L9: assumes "\<exists>! x. x\<in>A \<and> \<phi>(x)"
  shows 
  "\<exists>a. {x\<in>A. \<phi>(x)} = {a}"
  "\<Union> {x\<in>A. \<phi>(x)} \<in> A"
  "\<phi>(\<Union> {x\<in>A. \<phi>(x)})"
  "\<exists>x\<in>A. \<phi>(x)" 
proof -
  from assms(1) show "\<exists>a. {x\<in>A. \<phi>(x)} = {a}" by auto
  then obtain a where I: "{x\<in>A. \<phi>(x)} = {a}" by auto
  then have "\<Union> {x\<in>A. \<phi>(x)} = a" by auto
  moreover
  from I have "a \<in> {x\<in>A. \<phi>(x)}" by simp
  hence "a\<in>A" and "\<phi>(a)" by auto
  ultimately show "\<Union> {x\<in>A. \<phi>(x)} \<in> A" and "\<phi>(\<Union> {x\<in>A. \<phi>(x)})"
    by auto
  from assms show "\<exists>x\<in>A. \<phi>(x)" by auto
qed

text\<open>A simple version of \<open> ZF1_1_L9\<close>.\<close>

corollary singleton_extract: assumes  "\<exists>! x. x\<in>A"
  shows "(\<Union> A) \<in> A"
proof -
  from assms have "\<exists>! x. x\<in>A \<and> True" by simp
  then have "\<Union> {x\<in>A. True} \<in> A" by (rule ZF1_1_L9)
  thus "(\<Union> A) \<in> A" by simp
qed

text\<open>A criterion for when a set defined by comprehension is a singleton.\<close>

lemma singleton_comprehension: 
  assumes A1: "y\<in>X" and A2: "\<forall>x\<in>X. \<forall>y\<in>X. P(x) = P(y)"
  shows "(\<Union>{P(x). x\<in>X}) = P(y)"
proof - 
  let ?A = "{P(x). x\<in>X}"
  have "\<exists>! c. c \<in> ?A"
  proof
    from A1 show "\<exists>c. c \<in> ?A" by auto
  next
    fix a b assume "a \<in> ?A" and "b \<in> ?A"
    then obtain x t where 
      "x \<in> X" "a = P(x)" and "t \<in> X" "b = P(t)"
      by auto
    with A2 show "a=b" by blast
  qed
  then have "(\<Union>?A) \<in> ?A" by (rule singleton_extract)
  then obtain x where "x \<in> X" and "(\<Union>?A) = P(x)"
    by auto
  from A1 A2 \<open>x \<in> X\<close> have "P(x) = P(y)"
    by blast
  with \<open>(\<Union>?A) = P(x)\<close> show "(\<Union>?A) = P(y)" by simp
qed

text\<open>Adding an element of a set to that set does not change the set.\<close>

lemma set_elem_add: assumes "x\<in>X" shows "X \<union> {x} = X" using assms 
  by auto

text\<open>Here we define a restriction of a collection of sets to a given set. 
  In romantic math this is typically denoted $X\cap M$ and means 
  $\{X\cap A : A\in M \} $. Note there is also restrict$(f,A)$ 
  defined for relations in ZF.thy.\<close>

definition
  RestrictedTo (infixl "{restricted to}" 70) where
  "M {restricted to} X \<equiv> {X \<inter> A . A \<in> M}"

text\<open>A lemma on a union of a restriction of a collection
  to a set.\<close>

lemma union_restrict: 
  shows "\<Union>(M {restricted to} X) = (\<Union>M) \<inter> X"
  using RestrictedTo_def by auto

text\<open>Next we show a technical identity that is used to prove sufficiency 
  of some condition for a collection of sets to be a base for a topology.\<close>

lemma ZF1_1_L10: assumes A1: "\<forall>U\<in>C. \<exists>A\<in>B. U = \<Union>A" 
  shows "\<Union>\<Union> {\<Union>{A\<in>B. U = \<Union>A}. U\<in>C} = \<Union>C"
proof
  show "\<Union>(\<Union>U\<in>C. \<Union>{A \<in> B . U = \<Union>A}) \<subseteq> \<Union>C" by blast
  show "\<Union>C \<subseteq> \<Union>(\<Union>U\<in>C. \<Union>{A \<in> B . U = \<Union>A})"
  proof
    fix x assume "x \<in> \<Union>C" 
    show "x \<in> \<Union>(\<Union>U\<in>C. \<Union>{A \<in> B . U = \<Union>A})"
    proof -
      from \<open>x \<in> \<Union>C\<close> obtain U where "U\<in>C \<and> x\<in>U" by auto
      with A1 obtain A where "A\<in>B \<and> U = \<Union>A" by auto
      from \<open>U\<in>C \<and> x\<in>U\<close> \<open>A\<in>B \<and> U = \<Union>A\<close> show "x\<in> \<Union>(\<Union>U\<in>C. \<Union>{A \<in> B . U = \<Union>A})" 
	by auto
    qed
  qed
qed

text\<open>Standard Isabelle uses a notion of \<open>cons(A,a)\<close> that can be thought 
  of as $A\cup \{a\}$.\<close>

lemma consdef: shows "cons(a,A) = A \<union> {a}"
  using cons_def by auto

text\<open>If a difference between a set and a singleton is empty, then
  the set is empty or it is equal to the singleton.\<close>

lemma singl_diff_empty: assumes "A\<setminus>{x} = \<emptyset>"
  shows "A = \<emptyset> \<or> A = {x}"
  using assms by auto

text\<open>If a difference between a set and a singleton is the set, 
  then the only element of the singleton is not in the set.\<close>

lemma singl_diff_eq: assumes A1: "A\<setminus>{x} = A"
  shows "x \<notin> A"
proof -
  have "x \<notin> A - {x}" by auto
  with A1 show "x \<notin> A" by simp
qed

text\<open>Simple substitution in membership, has to be used by rule
  in very rare cases.\<close>

lemma eq_mem: assumes "x\<in>A" and "y=x" shows "y\<in>A" 
  using assms by simp

text\<open>A basic property of sets defined by comprehension.\<close>

lemma comprehension: assumes "a \<in> {x\<in>X. p(x)}"
  shows "a\<in>X" and "p(a)" using assms by auto

text\<open>A basic property of a set defined by another type of comprehension.\<close>

lemma comprehension_repl: assumes "y \<in> {p(x). x\<in>X}"
  shows "\<exists>x\<in>X. y = p(x)" using assms by auto

text\<open>The inverse of the \<open>comprehension\<close> lemma.\<close>

lemma mem_cond_in_set: assumes "\<phi>(c)" and "c\<in>X"
  shows "c \<in> {x\<in>X. \<phi>(x)}" using assms by blast

text\<open>The image of a set by a greater relation is greater. \<close>

lemma image_rel_mono: assumes "r\<subseteq>s" shows "r``(A) \<subseteq> s``(A)" 
  using assms by auto 

text\<open> A technical lemma about relations: if $x$ is in its image by a relation $U$
  and that image is contained in some set $C$, then the image of the singleton
  $\{ x\}$ by the relation $U \cup C\times C$ equals $C$. \<close>

lemma image_greater_rel: 
  assumes  "x \<in> U``{x}"  and "U``{x} \<subseteq> C"
  shows "(U \<union> C\<times>C)``{x} = C"
  using assms image_Un_left by blast 

text\<open>Reformulation of the definition of composition of two relations: \<close>

lemma rel_compdef: 
  shows "\<langle>x,z\<rangle> \<in> r O s  \<longleftrightarrow>  (\<exists>y. \<langle>x,y\<rangle> \<in> s \<and> \<langle>y,z\<rangle> \<in> r)" 
  unfolding comp_def by auto

text\<open>Domain and range of the relation of the form $\bigcup \{U\times U : U\in P\}$
  is $\bigcup P$: \<close>

lemma domain_range_sym: shows "domain(\<Union>{U\<times>U. U\<in>P}) = \<Union>P" and "range(\<Union>{U\<times>U. U\<in>P}) = \<Union>P" 
  by auto

text\<open>An identity for the square (in the sense of composition) of a symmetric relation.\<close>

lemma symm_sq_prod_image: assumes "converse(r) = r" 
  shows "r O r = \<Union>{(r``{x})\<times>(r``{x}). x \<in> domain(r)}"
proof
  { fix p assume "p \<in> r O r"
    then obtain y z where "\<langle>y,z\<rangle> = p" by auto
    with \<open>p \<in> r O r\<close> obtain x where "\<langle>y,x\<rangle> \<in> r" and "\<langle>x,z\<rangle> \<in> r"
      using rel_compdef by auto
    from \<open>\<langle>y,x\<rangle> \<in> r\<close> have "\<langle>x,y\<rangle> \<in> converse(r)" by simp
    with assms \<open>\<langle>x,z\<rangle> \<in> r\<close> \<open>\<langle>y,z\<rangle> = p\<close> have "\<exists>x\<in>domain(r). p \<in> (r``{x})\<times>(r``{x})"
      by auto
  } thus "r O r \<subseteq> (\<Union>{(r``{x})\<times>(r``{x}). x \<in> domain(r)})"
    by blast
  { fix x assume "x \<in> domain(r)"
    have "(r``{x})\<times>(r``{x}) \<subseteq> r O r"
    proof -
      { fix p assume "p \<in> (r``{x})\<times>(r``{x})"
        then obtain y z where "\<langle>y,z\<rangle> = p" "y \<in> r``{x}" "z \<in> r``{x}"
          by auto
        from \<open>y \<in> r``{x}\<close> have "\<langle>x,y\<rangle> \<in> r" by auto
        then have "\<langle>y,x\<rangle> \<in> converse(r)" by simp
        with assms \<open>z \<in> r``{x}\<close> \<open>\<langle>y,z\<rangle> = p\<close> have "p \<in> r O r" by auto
      } thus ?thesis  by auto
    qed
  } thus "(\<Union>{(r``{x})\<times>(r``{x}). x \<in> domain(r)}) \<subseteq> r O r" 
    by blast
qed 

text\<open>Square of a reflexive relation contains the relation.
  Recall that in ZF the identity function on $X$ is the same as the diagonal
  of $X\times X$, i.e. $id(X) = \{\langle x,x\rangle : x\in X\}$. \<close>

lemma refl_square_greater: assumes "r \<subseteq> X\<times>X" "id(X) \<subseteq> r"
  shows "r \<subseteq> r O r" using assms by auto

text\<open>A reflexive relation is contained in the union of products of its singleton images. \<close>

lemma refl_union_singl_image: 
  assumes "A \<subseteq> X\<times>X" and "id(X)\<subseteq>A" shows "A \<subseteq> \<Union>{A``{x}\<times>A``{x}. x \<in> X}" 
proof -
  { fix p assume "p\<in>A"
    with assms(1) obtain x y where "x\<in>X" "y\<in>X" and "p=\<langle>x,y\<rangle>" by auto
    with assms(2) \<open>p\<in>A\<close> have "\<exists>x\<in>X. p \<in> A``{x}\<times>A``{x}" by auto
  } thus ?thesis by auto
qed

text\<open>If the cartesian product of the images of $x$ and $y$ by a 
  symmetric relation $W$ has a nonempty intersection with $R$
  then $x$ is in relation $W\circ (R\circ W)$ with $y$. \<close>

lemma sym_rel_comp: 
  assumes "W=converse(W)" and "(W``{x})\<times>(W``{y}) \<inter> R \<noteq> \<emptyset>"
  shows "\<langle>x,y\<rangle> \<in> (W O (R O W))" 
proof -
  from assms(2) obtain s t where "s\<in>W``{x}" "t\<in>W``{y}" and "\<langle>s,t\<rangle>\<in>R"
    by blast
  then have "\<langle>x,s\<rangle> \<in> W" and "\<langle>y,t\<rangle> \<in> W" by auto
  from \<open>\<langle>x,s\<rangle> \<in> W\<close> \<open>\<langle>s,t\<rangle> \<in> R\<close> have "\<langle>x,t\<rangle> \<in> R O W" by auto
  from \<open>\<langle>y,t\<rangle> \<in> W\<close> have "\<langle>t,y\<rangle> \<in> converse(W)" by blast
  with assms(1) \<open>\<langle>x,t\<rangle> \<in> R O W\<close> show ?thesis by auto
qed

text\<open>Suppose we have two families of sets $\{ A(i)\}_{i\in I}$
  and $\{ B(i)\}_{i\in I}$, indexed by a nonepty set of indices $I$
  and such that for every index $i\in I$ we have inclusion
  $A(i)\circ A(i) \subseteq B(i)$. Then a similar inclusion holds
  for the products of the families, namely 
  $(\bigcap_{i\in I}A(i))\circ (\bigcap_{i\in I}A(i)) \subseteq (\bigcap_{i\in I}B(i)$.\<close>

lemma square_incl_product: assumes "I\<noteq>\<emptyset>" "\<forall>i\<in>I. A(i) O A(i) \<subseteq> B(i)"
  shows "(\<Inter>i\<in>I. A(i)) O (\<Inter>i\<in>I. A(i)) \<subseteq> (\<Inter>i\<in>I. B(i))"
  using assms by force

text\<open> It's hard to believe but there are cases where we have to reference this rule. \<close>

lemma set_mem_eq: assumes "x\<in>A" "A=B" shows "x\<in>B" using assms by simp

text\<open>Given some family $\mathcal{A}$ of subsets of $X$ we can define the family of supersets of
  $\mathcal{A}$. \<close>

definition
  "Supersets(X,\<A>) \<equiv> {B\<in>Pow(X). \<exists>A\<in>\<A>. A\<subseteq>B}"

text\<open>The family itself is in its supersets. \<close>

lemma superset_gen: assumes "A\<subseteq>X" "A\<in>\<A>" shows "A \<in> Supersets(X,\<A>)"
  using assms unfolding Supersets_def by auto 

text\<open>The whole space is a superset of any nonempty collection of its subsets. \<close>

lemma space_superset: assumes "\<A>\<noteq>\<emptyset>" "\<A>\<subseteq>Pow(X)" shows "X \<in> Supersets(X,\<A>)"
proof -
  from assms(1) obtain A where "A\<in>\<A>" by auto
  with assms(2) show ?thesis unfolding Supersets_def by auto
qed

text\<open>The collection of supersets of an empty set is empty. In particular
  the whole space $X$ is not a superset of an empty set. \<close>

lemma supersets_of_empty: shows "Supersets(X,\<emptyset>) = \<emptyset>"
  unfolding Supersets_def by auto

text\<open>However, when the space is empty the collection of supersets does not have
  to be empty - the collection of supersets of the singleton collection containing
  only the empty set is this collection. \<close>

lemma supersets_in_empty: shows "Supersets(\<emptyset>,{\<emptyset>}) = {\<emptyset>}"
  unfolding Supersets_def by auto

text\<open>This can be done by the auto method, but sometimes takes a long time. \<close>

lemma witness_exists: assumes "x\<in>X" and "\<phi>(x)" shows "\<exists>x\<in>X. \<phi>(x)"
  using assms by auto

text\<open>Another lemma that concludes existence of some set.\<close>

lemma witness_exists1: assumes "x\<in>X" "\<phi>(x)" "\<psi>(x)"
  shows "\<exists>x\<in>X. \<phi>(x) \<and> \<psi>(x)"
  using assms by auto

text\<open>The next lemma has to be used as a rule in some rare cases. \<close>

lemma exists_in_set: assumes "\<forall>x. x\<in>A \<longrightarrow> \<phi>(x)" shows "\<forall>x\<in>A. \<phi>(x)"
  using assms by simp

text\<open>If $x$ belongs to a set where a property holds, then the property holds
  for $x$. This has to be used as rule in rare cases. \<close>

lemma property_holds: assumes "\<forall>t\<in>X. \<phi>(t)" and "x\<in>X"
  shows "\<phi>(x)" using assms by simp

text\<open>Set comprehensions defined by equal expressions are the equal. 
  The second assertion is actually about functions, which are sets of pairs 
  as illustrated in lemma \<open>fun_is_set_of_pairs\<close> in \<open>func1.thy\<close>  \<close>

lemma set_comp_eq: assumes "\<forall>x\<in>X. p(x) = q(x)" 
  shows "{p(x). x\<in>X} = {q(x). x\<in>X}" and "{\<langle>x,p(x)\<rangle>. x\<in>X} = {\<langle>x,q(x)\<rangle>. x\<in>X}"
  using assms by auto

text\<open>If every element of a non-empty set $X\subseteq Y$ satisfies a condition
  then the set of elements of $Y$ that satisfy the condition is non-empty.\<close>

lemma non_empty_cond: assumes "X\<noteq>\<emptyset>" "X\<subseteq>Y" and "\<forall>x\<in>X. P(x)"
  shows "{x\<in>Y. P(x)} \<noteq> 0" using assms by auto 

text\<open>If $z$ is a pair, then the cartesian product of the singletons of its 
  elements is the same as the singleton $\{ z\}$.\<close> 

lemma pair_prod: assumes "z = \<langle>x,y\<rangle>" shows "{x}\<times>{y} = {z}"
  using assms by blast



end

