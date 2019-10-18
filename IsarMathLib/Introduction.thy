(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2008-2014  Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Introduction to the IsarMathLib project\<close>

theory Introduction imports ZF.equalities

begin

text\<open>This theory does not contain any formalized mathematics used in 
  other theories, but is an introduction to IsarMathLib project.\<close>

subsection\<open>How to read IsarMathLib proofs - a tutorial\<close>

text\<open>Isar (the Isabelle's formal proof language) was designed to be similar
  to the standard language of mathematics. Any person able to read proofs in
  a typical mathematical paper should be able to read and understand
  Isar proofs without having to learn a special proof language. 
  However, Isar is a formal proof language and as such it does contain a 
  couple of constructs whose meaning is hard to guess. In this tutorial 
  we will define a notion and prove an example theorem about that notion,
  explaining Isar syntax along the way. This tutorial may also serve as a 
  style guide for IsarMathLib contributors. Note that this tutorial
  aims to help in reading the presentation of the Isar language that is used
  in IsarMathLib proof document and HTML rendering on the 
  FormalMath.org site, but does not teach how to write proofs that can be
  verified by Isabelle. This presentation is different than the source 
  processed by Isabelle (the concept that the source and presentation 
  look different should be familiar to any LaTeX user). To learn
  how to write Isar proofs one needs to study the source of this tutorial as well.\<close>

text\<open>The first thing that mathematicians typically do is to define
  notions. In Isar this is done with the \<open>definition\<close> keyword.
  In our case we define a notion of two 
  sets being disjoint. We will use the infix notation, i.e. the string
  \<open>{is disjoint with}\<close> put between two sets to denote our notion 
  of disjointness. 
  The left side of the \<open>\<equiv>\<close> symbol is the notion 
  being defined, the right side says how we define it. In Isabelle \<open>0\<close>
  is used to denote both zero (of natural numbers) and the empty set, which is
  not surprising as those two things are the same in set theory.\<close>

definition 
  AreDisjoint (infix "{is disjoint with}" 90) where
  "A {is disjoint with} B \<equiv> A \<inter> B = 0"

text\<open>We are ready to prove a theorem. Here we show that the relation
  of being disjoint is symmetric. We start with one of the keywords
  ''theorem'', ''lemma'' or ''corollary''. In Isar they are synonymous.
  Then we provide a name for the theorem. In standard mathematics 
  theorems are numbered. In Isar we can do that too, but it is
  considered better to give theorems meaningful names.
  After the ''shows'' keyword we give the statement to show. The 
  \<open>\<longleftrightarrow>\<close> symbol denotes the equivalence in Isabelle/ZF. Here
  we want to show that "A is disjoint with B iff and only if B is disjoint 
  with A". To prove this fact we show two implications - the first one that 
  \<open>A {is disjoint with} B\<close> implies \<open>B {is disjoint with} A\<close>
  and then the converse one. Each of these implications is formulated
  as a statement to be proved and then proved in 
  a subproof like a mini-theorem.
  Each subproof uses a proof block to show the implication. Proof blocks
  are delimited with curly brackets in Isar. 
  Proof block is one of the constructs that
  does not exist in informal mathematics, so it may be confusing. 
  When reading a proof containing a proof block I suggest to focus first 
  on what is that we are proving in it. This can be done by looking
  at the first line or two of the block and then at the last statement. 
  In our case the block starts with 
  "assume \<open>A {is disjoint with} B\<close> and the last statement
  is "then have \<open>B {is disjoint with} A\<close>". It is a typical pattern 
  when someone needs to prove an implication: one assumes the antecedent
  and then shows that the consequent follows from this assumption.
  Implications are denoted with the 
  \<open>\<longrightarrow>\<close> symbol in Isabelle. 
  After we prove both implications we collect them 
  using the ''moreover'' construct. The keyword ''ultimately''
  indicates that what follows is the conclusion of the statements 
  collected with ''moreover''. The ''show'' keyword is like ''have'',
  except that it indicates that we have arrived at the claim of the 
  theorem (or a subproof).\<close>

theorem disjointness_symmetric: 
  shows "A {is disjoint with} B \<longleftrightarrow> B {is disjoint with} A"
proof -
  have "A {is disjoint with} B \<longrightarrow> B {is disjoint with} A"
  proof -
    { assume "A {is disjoint with} B"
      then have "A \<inter> B = 0" using AreDisjoint_def by simp
      hence "B \<inter> A = 0" by auto
      then have  "B {is disjoint with} A"
        using AreDisjoint_def by simp
    } thus ?thesis by simp
  qed
  moreover have "B {is disjoint with} A \<longrightarrow> A {is disjoint with} B"
  proof -
    { assume "B {is disjoint with} A"
      then have "B \<inter> A = 0" using AreDisjoint_def by simp
      hence "A \<inter> B = 0" by auto
      then have  "A {is disjoint with} B"
        using AreDisjoint_def by simp
    } thus ?thesis by simp
  qed
  ultimately show ?thesis by blast
qed

subsection\<open>Overview of the project\<close>

text\<open>
  The  \<open>Fol1\<close>, \<open> ZF1\<close> and \<open>Nat_ZF_IML\<close> theory 
  files contain some background material that is needed for 
  the remaining theories.

  \<open>Order_ZF\<close> and \<open>Order_ZF_1a\<close> reformulate 
  material from standard Isabelle's 
  \<open>Order\<close> theory in terms of non-strict (less-or-equal) 
  order relations.
  \<open>Order_ZF_1\<close> on the other hand directly continues the \<open>Order\<close>
  theory file using strict order relations (less and not equal). This is useful
  for translating theorems from Metamath.

  In \<open>NatOrder_ZF\<close> we prove that the usual order on natural numbers
  is linear.
  
  The \<open>func1\<close> theory provides basic facts about functions.
  \<open>func_ZF\<close> continues this development with more advanced
  topics that relate to algebraic properties of binary operations, 
  like lifting a binary operation to a function space,
  associative, commutative and distributive operations and properties
  of functions related to order relations. \<open>func_ZF_1\<close> is 
  about properties of functions related to order relations.

  The standard Isabelle's \<open>Finite\<close> theory defines the finite
  powerset of a set as a certain "datatype" (?) with some recursive
  properties. IsarMathLib's \<open>Finite1\<close> 
  and  \<open>Finite_ZF_1\<close> theories develop more facts about this notion. 
  These two theories are obsolete now. 
  They will be gradually replaced by an approach based on set theory
  rather than tools specific to Isabelle. This approach is presented
  in \<open>Finite_ZF\<close> theory file.

  In \<open>FinOrd_ZF\<close> we talk about ordered finite sets.

  The \<open>EquivClass1\<close> theory file is a reformulation of 
  the material in the standard
  Isabelle's \<open>EquivClass\<close> theory in the spirit of ZF set theory.
  
  \<open>FiniteSeq_ZF\<close> discusses the notion of finite sequences 
  (a.k.a. lists).

  \<open>InductiveSeq_ZF\<close> provides the definition and properties of
  (what is known in basic calculus as) sequences defined by induction, 
  i. e. by a formula of the form $a_0 = x,\ a_{n+1} = f(a_n)$.

  \<open>Fold_ZF\<close> shows how the familiar from functional 
  programming notion of fold can be interpreted in set theory.

  \<open>Partitions_ZF\<close> is about splitting a set into non-overlapping
  subsets. This is a common trick in proofs.

  \<open>Semigroup_ZF\<close> treats the expressions of the form 
  $a_0\cdot a_1\cdot .. \cdot a_n$, (i.e. products of finite sequences), 
  where "$\cdot$" is an associative binary operation.

  \<open>CommutativeSemigroup_ZF\<close> is another take on a similar subject.
  This time we consider the case when the operation is commutative
  and the result of depends only on the set of elements we are
  summing (additively speaking), but not the order.

  The \<open>Topology_ZF\<close> series covers basics of general topology: 
  interior, closure, boundary, compact sets, separation axioms and 
  continuous functions.
  
  \<open>Group_ZF\<close>, \<open>Group_ZF_1\<close>, \<open>Group_ZF_1b\<close> 
  and \<open>Group_ZF_2\<close>
  provide basic facts of the group theory. \<open>Group_ZF_3\<close> 
  considers the notion of almost homomorphisms that is nedeed for the 
  real numbers construction in \<open>Real_ZF\<close>.

  The \<open>TopologicalGroup\<close> connects the \<open>Topology_ZF\<close> and 
  \<open>Group_ZF\<close> series and starts the subject of topological groups
  with some basic definitions and facts.

  In \<open>DirectProduct_ZF\<close> we define direct product of groups and show
  some its basic properties.

  The \<open>OrderedGroup_ZF\<close> theory treats ordered groups. 
  This is a suprisingly large theory for such relatively obscure topic.
  
  \<open>Ring_ZF\<close> defines rings. \<open>Ring_ZF_1\<close> covers 
  the properties of  rings that are specific to the real numbers construction 
  in \<open>Real_ZF\<close>.

  The \<open>OrderedRing_ZF\<close> theory looks at the consequences of adding
  a linear order to the ring algebraic structure.
  
  \<open>Field_ZF\<close> and \<open>OrderedField_ZF\<close> contain basic facts
  about (you guessed it) fields and ordered fields. 
  
  \<open>Int_ZF_IML\<close> theory considers the integers 
  as a monoid (multiplication) and an abelian ordered group (addition). 
  In \<open>Int_ZF_1\<close> we show that integers form a commutative ring.
  \<open>Int_ZF_2\<close> contains some facts about slopes (almost homomorphisms 
  on integers) needed for real numbers construction, 
  used in \<open>Real_ZF_1\<close>.

  In the \<open>IntDiv_ZF_IML\<close> theory we translate some properties of the 
  integer quotient and reminder functions studied in the standard Isabelle's
  \<open>IntDiv_ZF\<close> theory to the notation used in IsarMathLib.
  
  The \<open>Real_ZF\<close> and \<open>Real_ZF_1\<close> theories 
  contain the construction of real numbers based on the paper \cite{Arthan2004}
  by R. D. Arthan (not Cauchy sequences, not Dedekind sections). 
  The heavy lifting
  is done mostly in \<open>Group_ZF_3\<close>, \<open>Ring_ZF_1\<close> 
  and \<open>Int_ZF_2\<close>. \<open>Real_ZF\<close> contains 
  the part of the construction that can be done
  starting from generic abelian groups (rather than additive group of integers).
  This allows to show that real numbers form a ring. 
  \<open>Real_ZF_1\<close> continues the construction using properties specific
  to the integers and showing that real numbers constructed this way
  form a complete ordered field.

 \<open>Cardinal_ZF\<close> provides a couple of theorems about cardinals that are mostly used for studying  
 properties of topological properties (yes, this is kind of meta). 
 The main result (proven without AC) is that if two sets can be injectively mapped into an 
 infinite cardinal, then so can be their union. 
 There is also a definition of the Axiom of Choice specific for a given cardinal 
 (so that the choice function exists for families of sets of given cardinality). 
 Some properties are proven for such predicates, like that for finite families of sets the choice 
 function always exists (in ZF) and that the axiom of choice for a larger cardinal implies 
 one for a smaller cardinal.

 \<open>Group_ZF_4\<close> considers conjugate of subgroup and defines simple groups. 
 A nice theorem here is that endomorphisms of an abelian group form a ring. 
 The first isomorphism theorem (a group homomorphism $h$ induces an isomorphism between the group 
 divided by the kernel of $h$ and the image of $h$) is proven.

 Turns out given a property of a topological space one can define a local version of a property in general. 
 This is studied in the the \<open>Topology_ZF_properties_2\<close> theory and applied to local 
 versions of the property of being finite or compact or Hausdorff 
 (i.e. locally finite, locally compact, locally Hausdorff).
 There are a couple of nice applications, like one-point compactification that allows to show 
 that every locally compact Hausdorff space is regular. 
 Also there are some results on the interplay between hereditability of a property and local properties.

  For a given surjection $f : X\rightarrow Y$, where $X$ is a topological space one can consider the 
  weakest topology on $Y$ which makes $f$ continuous, let's call it a quotient topology generated by $f$.  
  The quotient topology generated by an equivalence relation r on X is actually a special case 
  of this setup, where $f$ is the natural projection of $X$ on the quotient $X/r$. 
  The properties of these two ways of getting new topologies are studied in \<open>Topology_ZF_8\<close> 
  theory. The main result is that any quotient topology generated by a function is homeomorphic 
  to a topology given by an equivalence relation, so these two approaches to quotient 
  topologies are kind of equivalent.

  As we all know, automorphisms of a topological space form a group. This fact is proven in \<open>Topology_ZF_9\<close> 
  and the automorphism groups for co-cardinal, included-set, and excluded-set topologies are identified. 
  For order topologies it is shown that order isomorphisms are homeomorphisms of the topology induced by the order. 
  Properties preserved by continuous functions are studied and as an application it is shown 
  for example that quotient topological spaces of compact (or connected) spaces are compact (or connected, resp.)
 
  The \<open>Topology_ZF_10\<close> theory is about products of two topological spaces. 
  It is proven that if two spaces are $T_0$ (or $T_1$, $T_2$, regular, connected) then their product is as well.

  Given a total order on a set one can define a natural topology on it generated by taking the rays 
  and intervals as the base. The  \<open>Topology_ZF_11\<close> theory studies relations between the order 
  and various properties of generated topology. For example one can show that if the order topology 
  is connected, then the order is complete (in the sense that for each set bounded from above the 
  set of upper bounds has a minimum). For a given cardinal $\kappa$ we can consider 
  generalized notion of $\kappa-separability$. Turns out $\kappa$-separability is related to (order) 
  density of sets of cardinality $\kappa$ for order topologies.


  Being a topological group imposes additional structure on the topology of the group, in particular 
  its separation properties. In \<open>Topological_Group_ZF_1.thy\<close> theory it is shown that if 
  a topology is $T_0$, then it must be $T_3$ , and that the topology in a topological group 
  is always regular.

  For a given normal subgroup of a topological group we can define a topology on the quotient 
  group in a natural way. At the end of the \<open>Topological_Group_ZF_2.thy\<close> theory it is shown 
  that such topology on the quotient group makes it a topological group.

  The \<open>Topological_Group_ZF_3.thy\<close> theory studies the topologies on subgroups of a 
  topological group. A couple of nice basic properties are shown, like that the closure of a 
  subgroup is a subgroup, closure of a normal subgroup is normal and, a bit more surprising 
  (to me) property that every locally-compact subgroup of a $T_0$ group is closed.

  In \<open>Complex_ZF\<close> we construct complex numbers starting from
  a complete ordered field (a model of real numbers). We also define 
  the notation for writing about complex numbers and prove that the 
  structure of complex numbers constructed there satisfies the axioms
  of complex numbers used in Metamath.

  \<open>MMI_prelude\<close> defines the \<open>mmisar0\<close> context in which 
  most theorems translated from Metamath are proven. It also contains a 
  chapter explaining how the translation works.

  In the \<open>Metamath_interface\<close> theory we prove a theorem
  that the \<open>mmisar0\<close> context is valid (can be used) 
  in the \<open>complex0\<close> context. 
  All theories using the translated results will import the
  \<open>Metamath_interface\<close> theory. The \<open>Metamath_sampler\<close>
  theory provides some examples of using the translated theorems
  in the \<open>complex0\<close> context.

  The theories \<open>MMI_logic_and_sets\<close>, \<open>MMI_Complex\<close>, 
  \<open>MMI_Complex_1\<close> and \<open>MMI_Complex_2\<close>
  contain the theorems imported from the
  Metamath's set.mm database. As the translated proofs are rather verbose
  these theories are not printed in this proof document.
  The full list of translated facts can be found in the 
  \<open>Metamath_theorems.txt\<close> file included in the 
  IsarMathLib distribution.
  The \<open>MMI_examples\<close> provides some theorems imported from Metamath
  that are printed in this proof document as examples of how translated
  proofs look like.\<close>

end
