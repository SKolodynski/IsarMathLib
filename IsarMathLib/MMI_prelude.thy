(* 
    This file is a part of MMIsar - a translation of Metamath's set.mm to Isabelle 2005 (ZF logic).

    Copyright (C) 2006  Slawomir Kolodynski

    This program is free software; Redistribution and use in source and binary forms, 
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
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)
section \<open>Metamath introduction\<close>

theory MMI_prelude imports Order_ZF_1

begin

text\<open>Metamath's set.mm features a large (over 8000) collection of theorems 
  proven in the ZFC set theory. This theory is part of an attempt to translate
  those theorems to Isar so that they are available for Isabelle/ZF users.
  A total of about 1200 assertions have been translated, 600 of that 
  with proofs (the rest was proven automatically by Isabelle). 
  The translation was done with the support of the mmisar tool, whose source
  is included in the IsarMathLib distributions prior to version 1.6.4. 
  The translation tool was doing about 99 percent of work involved, with the rest
  mostly related to the difference between Isabelle/ZF and Metamath 
  metalogics. Metamath uses Tarski-Megill metalogic that does not have a notion
  of bound variables (see 
  \<open> http://planetx.cc.vt.edu/AsteroidMeta/Distinctors_vs_binders \<close>
  for details and discussion).
  The translation project is closed now as I decided that it was too boring 
  and tedious even with the support of mmisar software. Also, the translated
  proofs are not as readable as native Isar proofs which goes against IsarMathLib
  philosophy.\<close>

subsection\<open>Importing from Metamath - how is it done\<close>

text\<open>
  We are interested in importing the theorems about complex numbers
  that start from the "recnt" theorem on. This is done mostly automatically
  by the mmisar tool that is included in the IsarMathLib distributions prior
  to version 1.6.4.
  The tool works as follows:

  First it reads the list of (Metamath) names of theorems 
  that are already imported to IsarMathlib ("known theorems") 
  and the list of theorems that are intended to be imported in this 
  session ("new theorems"). 
  The new theorems are consecutive theorems about complex numbers
  as they appear in the Metamath database.
  Then mmisar creates a "Metamath script" that contains 
  Metamath commands that open a log file and put the statements
  and proofs of the new theorems in that file in a readable format. 
  The tool writes this script to a disk file and executes metamath 
  with standard input redirected from that file. Then the log file is read
  and its contents converted to the Isar format. In Metamath, 
  the proofs of theorems about complex numbers 
  depend only on 28 axioms of complex numbers and some basic logic and 
  set theory theorems.
  The tool finds which of these dependencies are not known yet and repeats 
  the process of getting their statements from Metamath as with the 
  new theorems. As a result of this process mmisar creates files 
  new\_theorems.thy, new\_deps.thy and new\_known\_theorems.txt.
  The file new\_theorems.thy contains the theorems (with proofs) 
  imported from Metamath in this session. These theorems are added
  (by hand) to the current \<open>MMI_Complex_ZF_x.thy\<close> file. 
  The file new\_deps.thy contains the 
  statements of new dependencies with generic proofs "by auto".
  These are added to the \<open>MMI_logic_and_sets.thy\<close>.
  Most of the dependencies can be proven automatically by Isabelle.
  However, some manual work has to be done for the dependencies
  that Isabelle can not prove by itself and to correct problems related
  to the fact that Metamath uses a metalogic based on 
  distinct variable constraints (Tarski-Megill metalogic), 
  rather than an explicit notion of free and bound variables.

  The old list of known theorems is replaced by the new list and
  mmisar is ready to convert the next batch of new theorems.
  Of course this rarely works in practice without tweaking the mmisar
  source files every time a new batch is processed.\<close>

subsection\<open>The context for Metamath theorems\<close>

text\<open>We list the Metamth's axioms of complex numbers
  and define notation here.\<close>

text\<open>The next definition is what Metamath $X\in V$ is
  translated to. I am not sure why it works, probably because
  Isabelle does a type inference and the "=" sign
  indicates that both sides are sets.\<close>

definition
  IsASet :: "i\<Rightarrow>o" ("_ isASet" [90] 90) where
  (*set_def[simp]: "X isASet \<equiv>  X = X"*)
  IsASet_def[simp]: "X isASet \<equiv>  X = X"

text\<open>The next locale sets up the context to which Metamath theorems
  about complex numbers are imported. It assumes the axioms
  of complex numbers and defines the notation used for complex numbers.
  
  One of the problems with importing theorems from Metamath is that
  Metamath allows direct infix notation for binary operations so 
  that the notation $a f b$ is allowed where $f$ is a function 
  (that is, a set of pairs). To my knowledge, 
  Isar allows only notation \<open>f`\<langle>a,b\<rangle>\<close> with a possibility of 
  defining a syntax say \<open>a \<ca> b\<close> to mean the same as \<open>f`\<langle>a,b\<rangle>\<close> 
  (please correct me if I am wrong here). This is why we have
  two objects for addition: one called \<open>caddset\<close> that represents
  the binary function, and the second one called \<open>ca\<close> which 
  defines the \<open>a \<ca> b\<close> notation for \<open>caddset`\<langle>a,b\<rangle>\<close>.
  The same applies to multiplication of real numbers.
  
  Another difficulty is that Metamath allows to define sets with syntax
  $\{ x | p\}$ where $p$ is some formula that (usually) depends on $x$.
  Isabelle allows the set comprehension like this only as a subset of another 
  set i.e. $\{x\in A . p(x)\}$. This forces us to have a sligtly different 
  definition of (complex) natural numbers, requiring explicitly that natural 
  numbers is a subset of reals. Because of that, the proofs of Metamath theorems 
  that reference the definition directly can not be imported. 
\<close>

locale MMIsar0 =
  fixes real ("\<real>")
  fixes complex ("\<complex>")
  fixes one ("\<one>")
  fixes zero ("\<zero>")
  fixes iunit ("\<i>")
  fixes caddset ("\<caddset>")
  fixes cmulset ("\<cmulset>")
  fixes lessrrel ("\<lsrset>")

  fixes ca (infixl "\<ca>" 69)
  defines ca_def: "a \<ca> b \<equiv> \<caddset>`\<langle>a,b\<rangle>"
  fixes cm (infixl "\<cdot>" 71)
  defines cm_def: "a \<cdot> b \<equiv> \<cmulset>`\<langle>a,b\<rangle>"
  fixes sub (infixl "\<cs>" 69)
  defines sub_def: "a \<cs> b \<equiv> \<Union> { x \<in> \<complex>. b \<ca> x = a }"
  fixes cneg ("\<cn>_" 95)
  defines cneg_def: "\<cn> a \<equiv> \<zero> \<cs> a"
  fixes cdiv (infixl "\<cdiv>" 70)
  defines cdiv_def: "a \<cdiv> b \<equiv> \<Union> { x \<in> \<complex>. b \<cdot> x = a }"
  fixes cpnf ("\<cpnf>")
  defines cpnf_def: "\<cpnf> \<equiv> \<complex>"
  fixes cmnf ("\<cmnf>")
  defines cmnf_def: "\<cmnf> \<equiv> {\<complex>}"
  fixes cxr ("\<real>\<^sup>*")
  defines cxr_def: "\<real>\<^sup>* \<equiv> \<real> \<union> {\<cpnf>,\<cmnf>}"
  fixes cxn ("\<nat>")
  defines cxn_def: "\<nat> \<equiv> \<Inter> {N \<in> Pow(\<real>). \<one> \<in> N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"
  fixes lessr (infix "\<lsr>" 68)
  defines lessr_def: "a \<lsr> b \<equiv> \<langle>a,b\<rangle> \<in> \<lsrset>"
  fixes cltrrset ("\<cltrrset>")
  defines cltrrset_def: 
  "\<cltrrset> \<equiv> (\<lsrset> \<inter> \<real>\<times>\<real>) \<union> {\<langle>\<cmnf>,\<cpnf>\<rangle>} \<union> 
  (\<real>\<times>{\<cpnf>}) \<union> ({\<cmnf>}\<times>\<real> )"
  fixes cltrr (infix "\<ls>" 68)
  defines cltrr_def: "a \<ls> b \<equiv> \<langle>a,b\<rangle> \<in> \<cltrrset>"
  fixes convcltrr (infix ">" 68)
  defines convcltrr_def: "a > b \<equiv> \<langle>a,b\<rangle> \<in> converse(\<cltrrset>)"
  fixes lsq (infix "\<lsq>" 68)
  defines lsq_def: "a \<lsq> b \<equiv> \<not> (b \<ls> a)"
  fixes two ("\<two>")
  defines two_def: "\<two> \<equiv> \<one>\<ca>\<one>"
  fixes three ("\<three>")
  defines three_def: "\<three> \<equiv> \<two>\<ca>\<one>"
  fixes four ("\<four>")
  defines four_def: "\<four> \<equiv> \<three>\<ca>\<one>"
  fixes five ("\<five>")
  defines five_def: "\<five> \<equiv> \<four>\<ca>\<one>"
  fixes six ("\<six>")
  defines six_def: "\<six> \<equiv> \<five>\<ca>\<one>"
  fixes seven ("\<seven>")
  defines seven_def: "\<seven> \<equiv> \<six>\<ca>\<one>"
  fixes eight ("\<eight>")
  defines eight_def: "\<eight> \<equiv> \<seven>\<ca>\<one>"
  fixes nine ("\<nine>")
  defines nine_def: "\<nine> \<equiv> \<eight>\<ca>\<one>"

  assumes MMI_pre_axlttri: 
  "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> (A \<lsr> B \<longleftrightarrow> \<not>(A=B \<or> B \<lsr> A))"
  assumes MMI_pre_axlttrn: 
  "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> ((A \<lsr> B \<and> B \<lsr> C) \<longrightarrow> A \<lsr> C)"
  assumes MMI_pre_axltadd:
  "A \<in> \<real> \<and> B \<in> \<real> \<and> C \<in> \<real> \<longrightarrow> (A \<lsr> B \<longrightarrow> C\<ca>A \<lsr> C\<ca>B)"
  assumes MMI_pre_axmulgt0:
  "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> ( \<zero> \<lsr> A \<and> \<zero> \<lsr> B \<longrightarrow> \<zero> \<lsr> A\<cdot>B)"
  assumes MMI_pre_axsup:
  "A \<subseteq> \<real> \<and> A \<noteq> 0 \<and> (\<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsr> x) \<longrightarrow>
  (\<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<lsr> y)) \<and> (\<forall>y\<in>\<real>. (y \<lsr> x \<longrightarrow> (\<exists>z\<in>A. y \<lsr> z))))"
  assumes MMI_axresscn: "\<real> \<subseteq> \<complex>"
  assumes MMI_ax1ne0: "\<one> \<noteq> \<zero>"
  assumes MMI_axcnex: "\<complex> isASet"
  assumes MMI_axaddopr: "\<caddset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex>"
  assumes MMI_axmulopr: "\<cmulset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex>"
  assumes MMI_axmulcom: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<cdot> B = B \<cdot> A"
  assumes MMI_axaddcl: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B \<in> \<complex>"
  assumes MMI_axmulcl: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<cdot> B \<in> \<complex>"
  assumes MMI_axdistr: 
  "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A\<cdot>(B \<ca> C) = A\<cdot>B \<ca> A\<cdot>C" 
  assumes MMI_axaddcom: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> A \<ca> B = B \<ca> A"
  assumes MMI_axaddass: 
  "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A \<ca> B \<ca> C = A \<ca> (B \<ca> C)"
  assumes MMI_axmulass: 
  "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> \<longrightarrow> A \<cdot> B \<cdot> C = A \<cdot> (B \<cdot> C)"
  assumes MMI_ax1re: "\<one> \<in> \<real>"
  assumes MMI_axi2m1: "\<i> \<cdot> \<i> \<ca> \<one> = \<zero>"
  assumes MMI_ax0id: "A \<in> \<complex> \<longrightarrow> A \<ca> \<zero> = A"
  assumes MMI_axicn: "\<i> \<in> \<complex>"
  assumes MMI_axnegex: "A \<in> \<complex> \<longrightarrow> ( \<exists> x \<in> \<complex>. ( A \<ca> x ) = \<zero> )"
  assumes MMI_axrecex: "A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> ( \<exists> x \<in> \<complex>. A \<cdot> x = \<one>)"
  assumes MMI_ax1id: "A \<in> \<complex> \<longrightarrow> A \<cdot> \<one> = A"
  assumes MMI_axaddrcl: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>"
  assumes MMI_axmulrcl: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<cdot> B \<in> \<real>"
  assumes MMI_axrnegex: "A \<in> \<real> \<longrightarrow> ( \<exists> x \<in> \<real>. A \<ca> x = \<zero> )"
  assumes MMI_axrrecex: "A \<in> \<real> \<and> A \<noteq> \<zero> \<longrightarrow> ( \<exists> x \<in> \<real>. A \<cdot> x = \<one> )"
  

end