(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2008  Slawomir Kolodynski

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

section \<open>First Order Logic\<close>

theory Fol1 imports ZF.Trancl

begin

text\<open>Isabelle/ZF builds on the first order logic. Almost everything
  one would like to have in this area is covered in the standard Isabelle 
  libraries. The material in this theory provides some lemmas that are
  missing or allow for a more readable proof style.\<close>


subsection\<open>Notions and lemmas in FOL\<close>

text\<open>This section contains mostly shortcuts and workarounds 
  that allow to use more readable coding style.\<close>

text\<open>The next lemma serves as a workaround to problems with applying 
  the definition of transitivity (of a relation) in our coding style 
  (any attempt to do
  something like \<open>using trans_def\<close> puts Isabelle in an 
  infinite loop).\<close>

lemma Fol1_L2: assumes 
  A1: "\<forall> x y z. \<langle>x, y\<rangle> \<in> r \<and> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r"
  shows "trans(r)"
proof -
  from A1 have
    "\<forall> x y z. \<langle>x, y\<rangle> \<in> r \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r"
    using imp_conj by blast
  then show ?thesis unfolding trans_def by blast
qed

text\<open>Another workaround for the problem of Isabelle simplifier looping when 
  the transitivity definition is used.\<close>

lemma Fol1_L3: assumes A1: "trans(r)" and A2: "\<langle> a,b\<rangle> \<in> r  \<and> \<langle> b,c\<rangle> \<in> r"
  shows "\<langle> a,c\<rangle> \<in> r"
proof -
  from A1 have  "\<forall>x y z. \<langle>x, y\<rangle> \<in> r \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r"
   unfolding trans_def by blast
  with A2 show ?thesis using imp_conj by fast
qed
  
text\<open>There is a problem with application of the definition of asymetry for
  relations. The next lemma is a workaround.\<close>

lemma Fol1_L4: 
  assumes A1: "antisym(r)" and A2: "\<langle> a,b\<rangle> \<in> r"   "\<langle> b,a\<rangle> \<in> r"  
  shows "a=b"
proof -
  from A1 have "\<forall> x y. \<langle> x,y\<rangle> \<in> r \<longrightarrow> \<langle> y,x\<rangle> \<in> r \<longrightarrow> x=y"
    unfolding antisym_def by blast
  with A2 show "a=b" using imp_conj by fast
qed

text\<open>The definition below implements a common idiom that states that 
  (perhaps under some assumptions) exactly one of given three statements 
  is true.\<close>

definition
  "Exactly_1_of_3_holds(p,q,r) \<equiv> 
  (p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"

text\<open>The next lemma allows to prove statements of the form 
  \<open>Exactly_1_of_3_holds(p,q,r)\<close>.\<close>

lemma Fol1_L5:
  assumes "p\<or>q\<or>r"
  and "p \<longrightarrow> \<not>q \<and> \<not>r"
  and "q \<longrightarrow> \<not>p \<and> \<not>r"
  and "r \<longrightarrow> \<not>p \<and> \<not>q"
  shows "Exactly_1_of_3_holds(p,q,r)"
proof -
  from assms have
    "(p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"
    by blast
  then show "Exactly_1_of_3_holds (p,q,r)"
    unfolding Exactly_1_of_3_holds_def by fast
qed

text\<open>If exactly one of $p,q,r$ holds and $p$ is not true, then
  $q$ or $r$.\<close>

lemma Fol1_L6: 
  assumes A1: "\<not>p" and A2: "Exactly_1_of_3_holds(p,q,r)" 
  shows "q\<or>r"
proof -
  from A2 have  
    "(p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"
    unfolding Exactly_1_of_3_holds_def by fast
  hence "p \<or> q \<or> r" by blast
  with A1 show "q \<or> r" by simp
qed

text\<open>If exactly one of $p,q,r$ holds and $q$ is true, then 
  $r$ can not be true.\<close>

lemma Fol1_L7:
  assumes A1: "q" and A2: "Exactly_1_of_3_holds(p,q,r)"
  shows "\<not>r"
proof -
   from A2 have  
    "(p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"
    unfolding Exactly_1_of_3_holds_def by fast
  with A1 show "\<not>r" by blast
qed

text\<open>The next lemma demonstrates an elegant form of the 
  \<open>Exactly_1_of_3_holds(p,q,r)\<close> predicate.\<close>

lemma Fol1_L8: 
  shows "Exactly_1_of_3_holds(p,q,r) \<longleftrightarrow> (p\<longleftrightarrow>q\<longleftrightarrow>r) \<and> \<not>(p\<and>q\<and>r)"
proof
  assume "Exactly_1_of_3_holds(p,q,r)"
  then have 
    "(p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"
    unfolding Exactly_1_of_3_holds_def by fast
  thus "(p\<longleftrightarrow>q\<longleftrightarrow>r) \<and> \<not>(p\<and>q\<and>r)" by blast
next assume "(p\<longleftrightarrow>q\<longleftrightarrow>r) \<and> \<not>(p\<and>q\<and>r)" 
  hence
    "(p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"
    by auto
  then show "Exactly_1_of_3_holds(p,q,r)"
    unfolding Exactly_1_of_3_holds_def by fast
qed

text\<open>A property of the \<open>Exactly_1_of_3_holds\<close> predicate.\<close>

lemma Fol1_L8A: assumes A1: "Exactly_1_of_3_holds(p,q,r)"
  shows "p \<longleftrightarrow> \<not>(q \<or> r)"
proof -
  from A1 have "(p\<or>q\<or>r) \<and> (p \<longrightarrow> \<not>q \<and> \<not>r) \<and> (q \<longrightarrow> \<not>p \<and> \<not>r) \<and> (r \<longrightarrow> \<not>p \<and> \<not>q)"
    unfolding Exactly_1_of_3_holds_def by fast
  then show "p \<longleftrightarrow> \<not>(q \<or> r)" by blast
qed

text\<open>Exclusive or definition. There is one also defined in the standard 
  Isabelle, denoted \<open>xor\<close>, but it relates to boolean values, 
  which are sets. Here we define a logical functor.\<close>

definition
  Xor (infixl "Xor" 66) where
  "p Xor q \<equiv> (p\<or>q) \<and> \<not>(p \<and> q)"

text\<open>The "exclusive or" is the same as negation of equivalence.\<close>

lemma Fol1_L9: shows "p Xor q \<longleftrightarrow> \<not>(p\<longleftrightarrow>q)"
  using Xor_def by auto

text\<open>Constructions from the same sets are the same.
  It is suprising but we do have to use this as a rule in rare cases.\<close>

lemma same_constr: assumes "x=y" shows "P(x) = P(y)"
  using assms by simp

text\<open>Equivalence relations are symmetric.\<close>

lemma equiv_is_sym: assumes A1: "equiv(X,r)" and A2: "\<langle>x,y\<rangle> \<in> r"
  shows  "\<langle>y,x\<rangle> \<in> r"
proof -
  from A1 have "sym(r)" using equiv_def by simp
  then have "\<forall>x y. \<langle>x,y\<rangle> \<in> r \<longrightarrow> \<langle>y,x\<rangle> \<in> r"
    unfolding sym_def by fast
  with A2 show "\<langle>y,x\<rangle> \<in> r" by blast
qed

text\<open>Applying a transformation to equal values yields equal results.\<close>

lemma apply_fun_eq: assumes "x=y" shows "\<phi>(x) = \<phi>(y)"
  using assms by simp

(* In Isabelle/ZF conjunction associates to the right!.
lemma test: assumes A1: "P" "Q\<and>R"
  shows "P\<and>Q\<and>R"
proof - 
  from A1 show "P\<and>Q\<and>R" by (rule one_more_conj);
qed;

*)
end
