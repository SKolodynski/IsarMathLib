(*   This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005, 2006, 2007  Slawomir Kolodynski

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
section \<open>More on order relations\<close>

theory Order_ZF_1 imports ZF.Order ZF1

begin

text\<open>In \<open>Order_ZF\<close> we define some notions related to order relations
  based on the nonstrict orders ($\leq $ type). Some people however prefer to talk
  about these notions in terms of the strict order relation ($<$ type). 
  This is the case for the standard Isabelle \<open>Order.thy\<close> and also for 
  Metamath. In this theory file we repeat some developments from \<open>Order_ZF\<close>
  using the strict order relation as a basis.This is mostly useful for Metamath 
  translation, but is also of some general interest. The names of theorems are 
  copied from Metamath.\<close>


subsection\<open>Definitions and basic properties\<close>

text\<open>In this section we introduce some definitions taken from Metamath and relate 
  them to the ones used by the standard Isabelle \<open>Order.thy\<close>.
\<close>

text\<open>The next definition is the strict version of the linear order.
  What we write as \<open>R Orders A\<close> is written $R Ord A$ in Metamath.
\<close>

definition
StrictOrder (infix "Orders" 65) where
  "R Orders A \<equiv> \<forall>x y z. (x\<in>A \<and> y\<in>A \<and> z\<in>A) \<longrightarrow> 
  (\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
  (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)"

text\<open>The definition of supremum for a (strict) linear order.\<close>

definition
  "Sup(B,A,R) \<equiv> 
  \<Union> {x \<in> A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> 
  (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> (\<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))}"

text\<open>Definition of infimum for a linear order. 
  It is defined in terms of supremum.\<close>

definition
  "Infim(B,A,R) \<equiv> Sup(B,A,converse(R))"

text\<open>If relation $R$ orders a set $A$, (in Metamath sense) then $R$ 
  is irreflexive, transitive and linear therefore is a total order on $A$ 
  (in Isabelle sense).\<close>

lemma orders_imp_tot_ord: assumes A1: "R Orders A"
  shows 
  "irrefl(A,R)"
  "trans[A](R)"
  "part_ord(A,R)"
  "linear(A,R)"
  "tot_ord(A,R)"
proof -
  from A1 have I:
    "\<forall>x y z. (x\<in>A \<and> y\<in>A \<and> z\<in>A) \<longrightarrow> 
    (\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
    (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)"
    unfolding StrictOrder_def by simp
  then have "\<forall>x\<in>A. \<langle>x,x\<rangle> \<notin> R" by blast
  then show "irrefl(A,R)" using irrefl_def by simp
  moreover
  from I have 
    "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. \<langle>x,y\<rangle> \<in> R \<longrightarrow> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R"
    by blast
  then show "trans[A](R)" unfolding trans_on_def by blast
  ultimately show "part_ord(A,R)" using part_ord_def
    by simp
  moreover
  from I have
    "\<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle> \<in> R \<or> x=y \<or> \<langle>y,x\<rangle> \<in> R"
    by blast
  then show "linear(A,R)" unfolding linear_def by blast
  ultimately show "tot_ord(A,R)" using tot_ord_def
    by simp
qed

text\<open>A converse of \<open>orders_imp_tot_ord\<close>. Together with that
  theorem this shows that Metamath's notion of an order relation is equivalent to
  Isabelles \<open>tot_ord\<close> predicate.\<close>

lemma tot_ord_imp_orders: assumes A1: "tot_ord(A,R)"
  shows "R Orders A"
proof -
  from A1 have 
    I: "linear(A,R)" and  
    II: "irrefl(A,R)" and 
    III: "trans[A](R)" and
    IV: "part_ord(A,R)"
    using tot_ord_def part_ord_def by auto
  from IV have "asym(R \<inter> A\<times>A)"
    using part_ord_Imp_asym by simp
  then have V: "\<forall>x y. \<langle>x,y\<rangle> \<in> (R \<inter> A\<times>A) \<longrightarrow> \<not>(\<langle>y,x\<rangle> \<in> (R \<inter> A\<times>A))"
    unfolding asym_def by blast
  from I have VI: "\<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle> \<in> R \<or> x=y \<or> \<langle>y,x\<rangle> \<in> R"
    unfolding linear_def by blast
  from III have VII:
    "\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. \<langle>x,y\<rangle> \<in> R \<longrightarrow> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R"
    unfolding trans_on_def by blast
  { fix x y z
    assume T: "x\<in>A" "y\<in>A" "z\<in>A"
    have "\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)"
    proof
      assume A2: "\<langle>x,y\<rangle> \<in> R"
      with V T have  "\<not>(\<langle>y,x\<rangle> \<in> R)" by blast
      moreover from II T A2 have "x\<noteq>y" using irrefl_def
	by auto
      ultimately show "\<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)" by simp
    next assume  "\<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)"
      with VI T show "\<langle>x,y\<rangle> \<in> R" by auto
    qed
    moreover from VII T have
      "\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R"
      by blast
    ultimately have "(\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
      (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)"
      by simp
  } then have "\<forall>x y z. (x\<in>A \<and> y\<in>A \<and> z\<in>A) \<longrightarrow> 
      (\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
      (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)"
    by auto
  then show "R Orders A" using StrictOrder_def by simp
qed
    
subsection\<open>Properties of (strict) total orders\<close>

text\<open>In this section we discuss the properties of strict order relations. 
  This continues the development contained in the standard Isabelle's 
  \<open>Order.thy\<close> with a view towards using the theorems 
  translated from Metamath.\<close>

text\<open>A relation orders a set iff the converse relation orders a set. Going
  one way we can use the the lemma \<open>tot_od_converse\<close> from the standard 
  Isabelle's \<open>Order.thy\<close>.The other way is a bit more complicated (note that
  in Isabelle for \<open>converse(converse(r)) = r\<close> one needs $r$ to consist
  of ordered pairs, which does not follow from the \<open>StrictOrder\<close> 
  definition above).\<close>

lemma cnvso: shows "R Orders A \<longleftrightarrow> converse(R) Orders A"
proof
  let ?r = "converse(R)"
  assume "R Orders A"
  then have "tot_ord(A,?r)" using orders_imp_tot_ord tot_ord_converse
    by simp
  then show "?r Orders A" using tot_ord_imp_orders
    by simp
next
  let ?r = "converse(R)"
  assume "?r Orders A"
  then have A2: "\<forall>x y z. (x\<in>A \<and> y\<in>A \<and> z\<in>A) \<longrightarrow> 
    (\<langle>x,y\<rangle> \<in> ?r \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> ?r)) \<and> 
    (\<langle>x,y\<rangle> \<in> ?r \<and> \<langle>y,z\<rangle> \<in> ?r \<longrightarrow> \<langle>x,z\<rangle> \<in> ?r)"
    using StrictOrder_def by simp
  { fix x y z
    assume "x\<in>A \<and> y\<in>A \<and> z\<in>A"
    with A2 have
      I: "\<langle>y,x\<rangle> \<in> ?r \<longleftrightarrow> \<not>(x=y \<or> \<langle>x,y\<rangle> \<in> ?r)" and
      II: "\<langle>y,x\<rangle> \<in> ?r \<and> \<langle>z,y\<rangle> \<in> ?r \<longrightarrow> \<langle>z,x\<rangle> \<in> ?r"
      by auto
    from I have "\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)"
      by auto
    moreover from II have "\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R"
      by auto
    ultimately have "(\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
      (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)" by simp
  } then have  "\<forall>x y z. (x\<in>A \<and> y\<in>A \<and> z\<in>A) \<longrightarrow> 
      (\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
      (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)"
    by auto
  then show "R Orders A" using StrictOrder_def by simp
qed

text\<open>Supremum is unique, if it exists.\<close>

lemma supeu: assumes A1: "R Orders A" and A2: "x\<in>A" and
  A3: "\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R" and A4: "\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R  \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R)"
   shows 
  "\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
proof
  from A2 A3 A4 show
    "\<exists> x. x\<in>A\<and>(\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
    by auto
next fix x\<^sub>1 x\<^sub>2
  assume A5:
    "x\<^sub>1 \<in> A \<and> (\<forall>y\<in>B. \<langle>x\<^sub>1,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<^sub>1\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
    "x\<^sub>2 \<in> A \<and> (\<forall>y\<in>B. \<langle>x\<^sub>2,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<^sub>2\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
  from A1 have "linear(A,R)" using orders_imp_tot_ord tot_ord_def
    by simp
  then have "\<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle> \<in> R \<or> x=y \<or> \<langle>y,x\<rangle> \<in> R"
    unfolding linear_def by blast
  with A5 have "\<langle>x\<^sub>1,x\<^sub>2\<rangle> \<in> R \<or> x\<^sub>1=x\<^sub>2 \<or> \<langle>x\<^sub>2,x\<^sub>1\<rangle> \<in> R" by blast
  moreover 
  { assume "\<langle>x\<^sub>1,x\<^sub>2\<rangle> \<in> R"
    with A5 obtain z where "z\<in>B" and "\<langle>x\<^sub>1,z\<rangle> \<in> R" by auto
    with A5 have False by auto }
  moreover
  { assume "\<langle>x\<^sub>2,x\<^sub>1\<rangle> \<in> R"
    with A5 obtain z where "z\<in>B" and "\<langle>x\<^sub>2,z\<rangle> \<in> R" by auto
    with A5 have False by auto }
  ultimately  show "x\<^sub>1 = x\<^sub>2" by auto
qed

text\<open>Supremum has expected properties if it exists.\<close>

lemma sup_props: assumes A1: "R Orders A" and 
  A2: "\<exists>x\<in>A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
  shows 
  "Sup(B,A,R) \<in> A"
  "\<forall>y\<in>B. \<langle>Sup(B,A,R),y\<rangle> \<notin> R"
  "\<forall>y\<in>A. \<langle>y,Sup(B,A,R)\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R )"
proof -
  let ?S = "{x\<in>A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R ) ) }"
  from A2 obtain x where 
    "x\<in>A" and "(\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R)" and "\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R)"
    by auto
  with A1 have I:
    "\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
    using supeu by simp
  then have "( \<Union>?S ) \<in> A" by (rule ZF1_1_L9)
  then show "Sup(B,A,R) \<in> A" using Sup_def by simp
  from I have II:
    "(\<forall>y\<in>B. \<langle>\<Union>?S ,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,\<Union>?S\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
    by (rule ZF1_1_L9)
  hence "\<forall>y\<in>B. \<langle>\<Union>?S,y\<rangle> \<notin> R" by blast
  moreover have III: "(\<Union>?S) = Sup(B,A,R)" using Sup_def by simp
  ultimately show "\<forall>y\<in>B. \<langle>Sup(B,A,R),y\<rangle> \<notin> R" by simp
  from II have IV: "\<forall>y\<in>A. \<langle>y,\<Union>?S\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R)"
    by blast
  { fix y assume A3: "y\<in>A" and "\<langle>y,Sup(B,A,R)\<rangle> \<in> R"
    with III have "\<langle>y,\<Union>?S\<rangle> \<in> R" by simp
    with IV A3 have "\<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R" by blast
  } thus  "\<forall>y\<in>A. \<langle>y,Sup(B,A,R)\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R )"
    by simp
qed

text\<open>Elements greater or equal than any element of $B$ are 
  greater or equal than supremum of $B$.\<close>

lemma supnub: assumes A1: "R Orders A" and A2: 
  "\<exists>x\<in>A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R))"
  and A3: "c \<in> A" and A4: "\<forall>z\<in>B. \<langle>c,z\<rangle> \<notin> R"
  shows "\<langle>c, Sup(B,A,R)\<rangle> \<notin> R"
proof -
  from A1 A2 have
    "\<forall>y\<in>A. \<langle>y,Sup(B,A,R)\<rangle> \<in> R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> R )"
    by (rule sup_props)
  with A3 A4 show "\<langle>c, Sup(B,A,R)\<rangle> \<notin> R" by auto
qed

end
