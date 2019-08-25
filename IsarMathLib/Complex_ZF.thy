(*   This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

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


section \<open>Complex numbers\<close>


theory Complex_ZF imports func_ZF_1 OrderedField_ZF

begin

text\<open>The goal of this theory is to define complex numbers
  and prove that the Metamath complex numbers axioms hold.\<close>

subsection\<open>From complete ordered fields to complex numbers\<close>

text\<open>This section consists mostly of definitions and a proof
  context for talking about complex numbers.
  Suppose we have a set $R$ with binary operations $A$ and
  $M$ and a relation $r$ such that the quadruple $(R,A,M,r)$
  forms a complete ordered field. 
  The next definitions take $(R,A,M,r)$ and
  construct the sets that represent the structure of complex numbers:
  the carrier ($\mathbb{C}=R\times R$), binary operations of 
  addition and multiplication of complex numbers and the order
  relation on $\mathbb{R}=R\times 0$.
  The \<open>ImCxAdd, ReCxAdd, ImCxMul, ReCxMul\<close> are helper
  meta-functions representing the imaginary part of a sum of
  complex numbers, the real part of a sum of real numbers, the
  imaginary part of a product of
  complex numbers and the real part of a product of real numbers,
  respectively. The actual operations (subsets of $(R\times R)\times R$ 
  are named \<open>CplxAdd\<close> and \<open>CplxMul\<close>.
  
  When $R$ is an ordered field, it comes with an order relation.
  This induces a natural strict order relation on 
  $\{\langle x,0\rangle : x\in R\}\subseteq R\times R$. We call the
  set $\{\langle x,0\rangle : x\in R\}$ \<open>ComplexReals(R,A)\<close>
  and the strict order relation \<open>CplxROrder(R,A,r)\<close>.
  The order on the real axis of complex numbers is defined
  as the relation induced on it by the
  canonical projection on the first coordinate and the order
  we have on the real numbers. 
  OK, lets repeat this slower.
  We start with the order relation $r$ on a (model of) real numbers $R$.
  We want to define an order relation on a subset of complex 
  numbers, namely on $R\times \{0\}$. To do that we use the notion of
  a relation induced by a mapping. The mapping here is
  $f:R\times \{0\}\rightarrow R, f\langle x,0 \rangle = x$ 
  which is defined under a name of 
  \<open>SliceProjection\<close> in \<open>func_ZF.thy\<close>. 
  This defines a relation $r_1$ (called \<open>InducedRelation(f,r)\<close>, 
  see \<open>func_ZF\<close>) on $R\times \{0\}$ such that 
  $ \langle \langle x, 0\rangle, \langle y,0\rangle 
  \in r_1$ iff $\langle x,y\rangle \in r$. This way we get what we call
  \<open>CplxROrder(R,A,r)\<close>. However, this is not the 
  end of the story, because Metamath uses strict inequalities in its axioms, 
  rather than weak ones like IsarMathLib (mostly). So we need to take
  the strict version of this order relation. This is done in
  the syntax definition of \<open>\<lsr>\<close> in the definition of 
  \<open>complex0\<close> context. Since Metamath proves a lot of theorems
  about the real numbers extended with $+\infty$ and $-\infty$, we define 
  the notation for inequalites on the extended real line as well.
\<close>

text\<open>A helper expression representing the real part
  of the sum of two complex numbers.\<close>

definition
  "ReCxAdd(R,A,a,b) \<equiv> A`\<langle>fst(a),fst(b)\<rangle>"

text\<open>An expression representing the imaginary part of the sum
  of two complex numbers.\<close>

definition
  "ImCxAdd(R,A,a,b) \<equiv> A`\<langle>snd(a),snd(b)\<rangle>"

text\<open>The set (function) that is the binary operation that adds complex numbers.\<close>

definition
  "CplxAdd(R,A) \<equiv> 
  {\<langle>p, \<langle> ReCxAdd(R,A,fst(p),snd(p)),ImCxAdd(R,A,fst(p),snd(p)) \<rangle> \<rangle>. 
  p\<in>(R\<times>R)\<times>(R\<times>R)}" 

text\<open>The expression representing the imaginary part of the
  product of complex numbers.\<close>

definition
  "ImCxMul(R,A,M,a,b) \<equiv> A`\<langle>M`\<langle>fst(a),snd(b)\<rangle>, M`\<langle>snd(a),fst(b)\<rangle> \<rangle>"

text\<open>The expression representing the real part of the
  product of complex numbers.\<close>

definition
  "ReCxMul(R,A,M,a,b) \<equiv> 
  A`\<langle>M`\<langle>fst(a),fst(b)\<rangle>,GroupInv(R,A)`(M`\<langle>snd(a),snd(b)\<rangle>)\<rangle>"

text\<open>The function (set) that represents the binary operation of 
  multiplication of complex numbers.\<close>

definition
  "CplxMul(R,A,M) \<equiv> 
  { \<langle>p, \<langle>ReCxMul(R,A,M,fst(p),snd(p)),ImCxMul(R,A,M,fst(p),snd(p))\<rangle> \<rangle>. 
  p \<in> (R\<times>R)\<times>(R\<times>R)}"

text\<open>The definition real numbers embedded in the complex plane.\<close>

definition
  "ComplexReals(R,A) \<equiv> R\<times>{TheNeutralElement(R,A)}"

text\<open>Definition of order relation on the real line.\<close>

definition
  "CplxROrder(R,A,r) \<equiv> 
  InducedRelation(SliceProjection(ComplexReals(R,A)),r)"

text\<open>The next locale defines proof context and notation that will be
  used for complex numbers.\<close>

locale complex0 =
  fixes R and A and M and r
  assumes R_are_reals: "IsAmodelOfReals(R,A,M,r)"

  fixes complex ("\<complex>")
  defines complex_def[simp]: "\<complex> \<equiv> R\<times>R"

  fixes rone ("\<one>\<^sub>R")
  defines rone_def[simp]: "\<one>\<^sub>R \<equiv> TheNeutralElement(R,M)"

  fixes rzero ("\<zero>\<^sub>R")
  defines rzero_def[simp]: "\<zero>\<^sub>R \<equiv> TheNeutralElement(R,A)"

  fixes one ("\<one>")
  defines one_def[simp]: "\<one> \<equiv> \<langle>\<one>\<^sub>R, \<zero>\<^sub>R\<rangle>"

  fixes zero ("\<zero>")
  defines zero_def[simp]: "\<zero> \<equiv> \<langle>\<zero>\<^sub>R, \<zero>\<^sub>R\<rangle>"

  fixes iunit ("\<i>")
  defines iunit_def[simp]: "\<i> \<equiv> \<langle>\<zero>\<^sub>R,\<one>\<^sub>R\<rangle>"

  fixes creal ("\<real>")
  defines creal_def[simp]: "\<real> \<equiv> {\<langle>r,\<zero>\<^sub>R\<rangle>. r\<in>R}"

  fixes rmul (infixl "\<rmu>" 71)
  defines rmul_def[simp]: "a \<rmu> b \<equiv> M`\<langle>a,b\<rangle>"

  fixes radd (infixl "\<ra>" 69)
  defines radd_def[simp]: "a \<ra> b \<equiv> A`\<langle>a,b\<rangle>"

  fixes rneg ("\<rm> _" 70)
  defines rneg_def[simp]: "\<rm> a \<equiv>  GroupInv(R,A)`(a)"

  fixes ca (infixl "\<ca>" 69)
  defines ca_def[simp]: "a \<ca> b \<equiv> CplxAdd(R,A)`\<langle>a,b\<rangle>"

  fixes cm (infixl "\<cdot>" 71)
  defines cm_def[simp]: "a \<cdot> b \<equiv> CplxMul(R,A,M)`\<langle>a,b\<rangle>"

  fixes cdiv (infixl "\<cdiv>" 70)
  defines cdiv_def[simp]: "a \<cdiv> b \<equiv> \<Union> { x \<in> \<complex>. b \<cdot> x = a }"

  fixes sub (infixl "\<cs>" 69)
  defines sub_def[simp]: "a \<cs> b \<equiv> \<Union> { x \<in> \<complex>. b \<ca> x = a }"

  fixes cneg ("\<cn>_" 95)
  defines cneg_def[simp]: "\<cn> a \<equiv> \<zero> \<cs> a"
  
  fixes lessr (infix "\<lsr>" 68)
  defines lessr_def[simp]: 
  "a \<lsr> b \<equiv> \<langle>a,b\<rangle> \<in> StrictVersion(CplxROrder(R,A,r))"

  fixes cpnf ("\<cpnf>")
  defines cpnf_def[simp]: "\<cpnf> \<equiv> \<complex>"

  fixes cmnf ("\<cmnf>")
  defines cmnf_def[simp]: "\<cmnf> \<equiv> {\<complex>}"

  fixes cxr ("\<real>\<^sup>*")
  defines cxr_def[simp]: "\<real>\<^sup>* \<equiv> \<real> \<union> {\<cpnf>,\<cmnf>}"

  fixes cxn ("\<nat>")
  defines cxn_def[simp]: 
  "\<nat> \<equiv> \<Inter> {N \<in> Pow(\<real>). \<one> \<in> N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"

  fixes cltrrset ("\<cltrrset>")
  defines cltrrset_def[simp]: 
  "\<cltrrset> \<equiv>  StrictVersion(CplxROrder(R,A,r)) \<inter> \<real>\<times>\<real> \<union>
  {\<langle>\<cmnf>,\<cpnf>\<rangle>} \<union> (\<real>\<times>{\<cpnf>}) \<union> ({\<cmnf>}\<times>\<real> )"

  fixes cltrr (infix "\<ls>" 68)
  defines cltrr_def[simp]: "a \<ls> b \<equiv> \<langle>a,b\<rangle> \<in> \<cltrrset>"

  fixes lsq (infix "\<lsq>" 68)
  defines lsq_def[simp]: "a \<lsq> b \<equiv> \<not> (b \<ls> a)"

  fixes two ("\<two>")
  defines two_def[simp]: "\<two> \<equiv> \<one> \<ca> \<one>"

  fixes three ("\<three>")
  defines three_def[simp]: "\<three> \<equiv> \<two>\<ca>\<one>"

  fixes four ("\<four>")
  defines four_def[simp]: "\<four> \<equiv> \<three>\<ca>\<one>"

  fixes five ("\<five>")
  defines five_def[simp]: "\<five> \<equiv> \<four>\<ca>\<one>"

  fixes six ("\<six>")
  defines six_def[simp]: "\<six> \<equiv> \<five>\<ca>\<one>"

  fixes seven ("\<seven>")
  defines seven_def[simp]: "\<seven> \<equiv> \<six>\<ca>\<one>"

  fixes eight ("\<eight>")
  defines eight_def[simp]: "\<eight> \<equiv> \<seven>\<ca>\<one>"

  fixes nine ("\<nine>")
  defines nine_def[simp]: "\<nine> \<equiv> \<eight>\<ca>\<one>"

subsection\<open>Axioms of complex numbers\<close>

text\<open>In this section we will prove that all Metamath's axioms of complex
  numbers hold in the \<open>complex0\<close> context.\<close>

text\<open>The next lemma lists some contexts that are valid in the \<open>complex0\<close>
  context.\<close>

lemma (in complex0) valid_cntxts: shows
  "field1(R,A,M,r)"
  "field0(R,A,M)"
  "ring1(R,A,M,r)"
  "group3(R,A,r)"
  "ring0(R,A,M)"
  "M {is commutative on} R"
  "group0(R,A)"
proof -
  from R_are_reals have I: "IsAnOrdField(R,A,M,r)"
    using IsAmodelOfReals_def by simp
  then show "field1(R,A,M,r)" using OrdField_ZF_1_L2 by simp
  then show "ring1(R,A,M,r)" and I: "field0(R,A,M)"
    using field1.axioms ring1_def field1.OrdField_ZF_1_L1B
    by auto
  then show "group3(R,A,r)" using ring1.OrdRing_ZF_1_L4
    by simp
  from I have "IsAfield(R,A,M)" using field0.Field_ZF_1_L1
    by simp
  then have "IsAring(R,A,M)" and "M {is commutative on} R"
    using IsAfield_def by auto
  then show "ring0(R,A,M)" and "M {is commutative on} R" 
    using ring0_def by auto
  then show "group0(R,A)" using ring0.Ring_ZF_1_L1
    by simp
qed

text\<open>The next lemma shows the definition of real and imaginary part of
  complex sum and product in a more readable form using notation defined
  in \<open>complex0\<close> locale.\<close>

lemma (in complex0) cplx_mul_add_defs: shows
  "ReCxAdd(R,A,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = a \<ra> c"
  "ImCxAdd(R,A,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = b \<ra> d"
  "ImCxMul(R,A,M,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = a\<rmu>d \<ra> b\<rmu>c"
  "ReCxMul(R,A,M,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) =  a\<rmu>c \<ra> (\<rm>b\<rmu>d)"
proof -
  let ?z\<^sub>1 = "\<langle>a,b\<rangle>"
  let ?z\<^sub>2 = "\<langle>c,d\<rangle>"
  have "ReCxAdd(R,A,?z\<^sub>1,?z\<^sub>2) \<equiv>  A`\<langle>fst(?z\<^sub>1),fst(?z\<^sub>2)\<rangle>"
   by (rule ReCxAdd_def)
  moreover have "ImCxAdd(R,A,?z\<^sub>1,?z\<^sub>2) \<equiv>  A`\<langle>snd(?z\<^sub>1),snd(?z\<^sub>2)\<rangle>"
    by (rule ImCxAdd_def)
  moreover have 
    "ImCxMul(R,A,M,?z\<^sub>1,?z\<^sub>2) \<equiv> A`\<langle>M`<fst(?z\<^sub>1),snd(?z\<^sub>2)>,M`<snd(?z\<^sub>1),fst(?z\<^sub>2)>\<rangle>"
    by (rule ImCxMul_def)
  moreover have
    "ReCxMul(R,A,M,?z\<^sub>1,?z\<^sub>2) \<equiv> 
    A`\<langle>M`<fst(?z\<^sub>1),fst(?z\<^sub>2)>,GroupInv(R,A)`(M`\<langle>snd(?z\<^sub>1),snd(?z\<^sub>2)\<rangle>)\<rangle>"
    by (rule ReCxMul_def)
  ultimately show 
    "ReCxAdd(R,A,?z\<^sub>1,?z\<^sub>2) =  a \<ra> c"
    "ImCxAdd(R,A,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = b \<ra> d"
    "ImCxMul(R,A,M,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) = a\<rmu>d \<ra> b\<rmu>c"
    "ReCxMul(R,A,M,\<langle>a,b\<rangle>,\<langle>c,d\<rangle>) =  a\<rmu>c \<ra> (\<rm>b\<rmu>d)"
    by auto
qed

text\<open>Real and imaginary parts of sums and products of complex numbers
  are real.\<close>

lemma (in complex0) cplx_mul_add_types: 
  assumes A1: "z\<^sub>1 \<in> \<complex>"   "z\<^sub>2 \<in> \<complex>"
  shows 
  "ReCxAdd(R,A,z\<^sub>1,z\<^sub>2) \<in> R"
  "ImCxAdd(R,A,z\<^sub>1,z\<^sub>2) \<in> R"
  "ImCxMul(R,A,M,z\<^sub>1,z\<^sub>2) \<in> R"
  "ReCxMul(R,A,M,z\<^sub>1,z\<^sub>2) \<in> R"
proof -
  let ?a = "fst(z\<^sub>1)"
  let ?b = "snd(z\<^sub>1)"
  let ?c = "fst(z\<^sub>2)"
  let ?d = "snd(z\<^sub>2)"
  from A1 have "?a \<in> R"  "?b \<in> R"  "?c \<in> R"  "?d \<in> R"
    by auto
  then have 
    "?a \<ra> ?c \<in> R"
    "?b \<ra> ?d \<in> R"
    "?a\<rmu>?d \<ra> ?b\<rmu>?c \<in> R"
    "?a\<rmu>?c \<ra> (\<rm> ?b\<rmu>?d) \<in> R"
    using valid_cntxts ring0.Ring_ZF_1_L4 by auto
  with A1 show 
    "ReCxAdd(R,A,z\<^sub>1,z\<^sub>2) \<in> R"
    "ImCxAdd(R,A,z\<^sub>1,z\<^sub>2) \<in> R"
    "ImCxMul(R,A,M,z\<^sub>1,z\<^sub>2) \<in> R"
    "ReCxMul(R,A,M,z\<^sub>1,z\<^sub>2) \<in> R"
    using cplx_mul_add_defs by auto
qed

text\<open>Complex reals are complex. Recall the definition of \<open>\<real>\<close>
  in the \<open>complex0\<close> locale.\<close>
  
lemma (in complex0) axresscn: shows "\<real> \<subseteq> \<complex>"
  using valid_cntxts group0.group0_2_L2 by auto

text\<open>Complex $1$ is not complex $0$.\<close>

lemma (in complex0) ax1ne0: shows "\<one> \<noteq> \<zero>"
proof -
  have "IsAfield(R,A,M)" using valid_cntxts field0.Field_ZF_1_L1
    by simp
  then show "\<one> \<noteq> \<zero>" using IsAfield_def by auto
qed

text\<open>Complex addition is a complex valued binary
  operation on complex numbers.\<close>

lemma (in complex0) axaddopr: shows "CplxAdd(R,A): \<complex> \<times> \<complex> \<rightarrow> \<complex>"
proof -
  have "\<forall>p \<in> \<complex>\<times>\<complex>. 
    \<langle>ReCxAdd(R,A,fst(p),snd(p)),ImCxAdd(R,A,fst(p),snd(p))\<rangle> \<in> \<complex>"
    using cplx_mul_add_types by simp
  then have 
    "{\<langle>p,\<langle>ReCxAdd(R,A,fst(p),snd(p)),ImCxAdd(R,A,fst(p),snd(p))\<rangle> \<rangle>. 
    p \<in> \<complex>\<times>\<complex>}: \<complex>\<times>\<complex> \<rightarrow> \<complex>"
    by (rule ZF_fun_from_total)
  then show "CplxAdd(R,A): \<complex> \<times> \<complex> \<rightarrow> \<complex>" using CplxAdd_def by simp
qed

text\<open>Complex multiplication is a complex valued binary
  operation on complex numbers.\<close>

lemma (in complex0) axmulopr: shows "CplxMul(R,A,M): \<complex> \<times> \<complex> \<rightarrow> \<complex>"
proof -
  have "\<forall>p \<in> \<complex>\<times>\<complex>. 
    \<langle>ReCxMul(R,A,M,fst(p),snd(p)),ImCxMul(R,A,M,fst(p),snd(p))\<rangle> \<in> \<complex>"
    using cplx_mul_add_types by simp
  then have
   "{\<langle>p,\<langle>ReCxMul(R,A,M,fst(p),snd(p)),ImCxMul(R,A,M,fst(p),snd(p))\<rangle>\<rangle>. 
    p \<in> \<complex>\<times>\<complex>}: \<complex>\<times>\<complex> \<rightarrow> \<complex>" by (rule ZF_fun_from_total)
  then show "CplxMul(R,A,M): \<complex> \<times> \<complex> \<rightarrow> \<complex>" using CplxMul_def by simp
qed

text\<open>What are the values of omplex addition and multiplication
  in terms of their real and imaginary parts?\<close>

lemma (in complex0) cplx_mul_add_vals: 
  assumes A1: "a\<in>R"  "b\<in>R"  "c\<in>R"  "d\<in>R"
  shows 
  "\<langle>a,b\<rangle> \<ca> \<langle>c,d\<rangle> = \<langle>a \<ra> c, b \<ra> d\<rangle>"
  "\<langle>a,b\<rangle> \<cdot> \<langle>c,d\<rangle> = \<langle>a\<rmu>c \<ra> (\<rm>b\<rmu>d), a\<rmu>d \<ra> b\<rmu>c\<rangle>"
proof -
  let ?S = "CplxAdd(R,A)" 
  let ?P = "CplxMul(R,A,M)"
  let ?p = "\<langle> \<langle>a,b\<rangle>, \<langle>c,d\<rangle> \<rangle>"
  from A1 have "?S : \<complex> \<times> \<complex> \<rightarrow> \<complex>" and "?p \<in> \<complex> \<times> \<complex>" 
    using axaddopr by auto
  moreover have
    "?S = {\<langle>p, <ReCxAdd(R,A,fst(p),snd(p)),ImCxAdd(R,A,fst(p),snd(p))>\<rangle>. 
    p \<in> \<complex> \<times> \<complex>}"
    using CplxAdd_def by simp
  ultimately have "?S`(?p) = \<langle>ReCxAdd(R,A,fst(?p),snd(?p)),ImCxAdd(R,A,fst(?p),snd(?p))\<rangle>"
    by (rule ZF_fun_from_tot_val)
  then show "\<langle>a,b\<rangle> \<ca> \<langle>c,d\<rangle> = \<langle>a \<ra> c, b \<ra> d\<rangle>"
    using cplx_mul_add_defs by simp
  from A1 have "?P : \<complex> \<times> \<complex> \<rightarrow> \<complex>" and "?p \<in> \<complex> \<times> \<complex>" 
    using axmulopr by auto
  moreover have 
    "?P = {\<langle>p, \<langle>ReCxMul(R,A,M,fst(p),snd(p)),ImCxMul(R,A,M,fst(p),snd(p))\<rangle> \<rangle>. 
    p \<in> \<complex> \<times> \<complex>}"
    using CplxMul_def by simp
  ultimately have 
    "?P`(?p) = \<langle>ReCxMul(R,A,M,fst(?p),snd(?p)),ImCxMul(R,A,M,fst(?p),snd(?p))\<rangle>"
    by (rule ZF_fun_from_tot_val)
  then show "\<langle>a,b\<rangle> \<cdot> \<langle>c,d\<rangle> = \<langle>a\<rmu>c \<ra> (\<rm>b\<rmu>d), a\<rmu>d \<ra> b\<rmu>c\<rangle>"
    using cplx_mul_add_defs by simp
qed

text\<open>Complex multiplication is commutative.\<close>

lemma (in complex0) axmulcom: assumes A1: "a \<in> \<complex>"  "b \<in> \<complex>"
  shows "a\<cdot>b = b\<cdot>a"
  using assms cplx_mul_add_vals valid_cntxts ring0.Ring_ZF_1_L4 
      field0.field_mult_comm by auto

text\<open>A sum of complex numbers is complex.\<close>

lemma (in complex0) axaddcl: assumes "a \<in> \<complex>"  "b \<in> \<complex>"
  shows "a\<ca>b \<in> \<complex>"
  using assms axaddopr apply_funtype by simp

text\<open>A product of complex numbers is complex.\<close>

lemma (in complex0) axmulcl: assumes "a \<in> \<complex>"  "b \<in> \<complex>"
  shows  "a\<cdot>b \<in> \<complex>"
  using assms axmulopr apply_funtype by simp

text\<open>Multiplication is distributive with respect to
  addition.\<close>

lemma (in complex0) axdistr: 
  assumes A1: "a \<in> \<complex>"  "b \<in> \<complex>"  "c \<in> \<complex>"
  shows "a\<cdot>(b \<ca> c) = a\<cdot>b \<ca> a\<cdot>c"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?a\<^sub>i = "snd(a)"
  let ?b\<^sub>r = "fst(b)"
  let ?b\<^sub>i = "snd(b)"
  let ?c\<^sub>r = "fst(c)"
  let ?c\<^sub>i = "snd(c)"  
  from A1 have T: 
    "?a\<^sub>r \<in> R"  "?a\<^sub>i \<in> R"  "?b\<^sub>r \<in> R"  "?b\<^sub>i \<in> R"  "?c\<^sub>r \<in> R"  "?c\<^sub>i \<in> R"
    "?b\<^sub>r\<ra>?c\<^sub>r \<in> R"  "?b\<^sub>i\<ra>?c\<^sub>i \<in> R"
    "?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i) \<in> R"
    "?a\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?c\<^sub>i) \<in> R"
    "?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r \<in> R"
    "?a\<^sub>r\<rmu>?c\<^sub>i \<ra> ?a\<^sub>i\<rmu>?c\<^sub>r \<in> R"
    using valid_cntxts ring0.Ring_ZF_1_L4 by auto
  with A1 have "a\<cdot>(b \<ca> c) = 
    \<langle>?a\<^sub>r\<rmu>(?b\<^sub>r\<ra>?c\<^sub>r) \<ra> (\<rm>?a\<^sub>i\<rmu>(?b\<^sub>i\<ra>?c\<^sub>i)),?a\<^sub>r\<rmu>(?b\<^sub>i\<ra>?c\<^sub>i) \<ra> ?a\<^sub>i\<rmu>(?b\<^sub>r\<ra>?c\<^sub>r)\<rangle>"
    using cplx_mul_add_vals by auto
  moreover from T have
    "?a\<^sub>r\<rmu>(?b\<^sub>r\<ra>?c\<^sub>r) \<ra> (\<rm>?a\<^sub>i\<rmu>(?b\<^sub>i\<ra>?c\<^sub>i)) =
    ?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i) \<ra> (?a\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?c\<^sub>i))"
    and
    "?a\<^sub>r\<rmu>(?b\<^sub>i\<ra>?c\<^sub>i) \<ra> ?a\<^sub>i\<rmu>(?b\<^sub>r\<ra>?c\<^sub>r) =
    ?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r \<ra> (?a\<^sub>r\<rmu>?c\<^sub>i \<ra> ?a\<^sub>i\<rmu>?c\<^sub>r)"
    using valid_cntxts ring0.Ring_ZF_2_L6 by auto
  moreover from A1 T have 
    "\<langle>?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i) \<ra> (?a\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?c\<^sub>i)),
    ?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r \<ra> (?a\<^sub>r\<rmu>?c\<^sub>i \<ra> ?a\<^sub>i\<rmu>?c\<^sub>r)\<rangle> =
    a\<cdot>b \<ca> a\<cdot>c"
    using cplx_mul_add_vals by auto
  ultimately show "a\<cdot>(b \<ca> c) = a\<cdot>b \<ca> a\<cdot>c"
    by simp
qed

text\<open>Complex addition is commutative.\<close>

lemma (in complex0) axaddcom: assumes "a \<in> \<complex>"  "b \<in> \<complex>"
  shows "a\<ca>b = b\<ca>a"
  using assms cplx_mul_add_vals valid_cntxts ring0.Ring_ZF_1_L4
  by auto

text\<open>Complex addition is associative.\<close>

lemma (in complex0) axaddass: assumes A1: "a \<in> \<complex>"  "b \<in> \<complex>"  "c \<in> \<complex>"
  shows "a \<ca> b \<ca> c = a \<ca> (b \<ca> c)"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?a\<^sub>i = "snd(a)"
  let ?b\<^sub>r = "fst(b)"
  let ?b\<^sub>i = "snd(b)"
  let ?c\<^sub>r = "fst(c)"
  let ?c\<^sub>i = "snd(c)"  
  from A1 have T: 
    "?a\<^sub>r \<in> R"  "?a\<^sub>i \<in> R"  "?b\<^sub>r \<in> R"  "?b\<^sub>i \<in> R"  "?c\<^sub>r \<in> R"  "?c\<^sub>i \<in> R"
    "?a\<^sub>r\<ra>?b\<^sub>r \<in> R"  "?a\<^sub>i\<ra>?b\<^sub>i \<in> R"  
    "?b\<^sub>r\<ra>?c\<^sub>r \<in> R"  "?b\<^sub>i\<ra>?c\<^sub>i \<in> R"
    using valid_cntxts ring0.Ring_ZF_1_L4 by auto
  with A1 have "a \<ca> b \<ca> c = \<langle>?a\<^sub>r\<ra>?b\<^sub>r\<ra>?c\<^sub>r,?a\<^sub>i\<ra>?b\<^sub>i\<ra>?c\<^sub>i\<rangle>"
    using cplx_mul_add_vals by auto
  also from A1 T have "\<dots> = a \<ca> (b \<ca> c)"
    using valid_cntxts ring0.Ring_ZF_1_L11 cplx_mul_add_vals
    by auto
  finally show "a \<ca> b \<ca> c = a \<ca> (b \<ca> c)"
    by simp
qed

text\<open>Complex multiplication is associative.\<close>

lemma (in complex0) axmulass: assumes A1: "a \<in> \<complex>"  "b \<in> \<complex>"  "c \<in> \<complex>"
  shows "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?a\<^sub>i = "snd(a)"
  let ?b\<^sub>r = "fst(b)"
  let ?b\<^sub>i = "snd(b)"
  let ?c\<^sub>r = "fst(c)"
  let ?c\<^sub>i = "snd(c)"
  from A1 have T:
    "?a\<^sub>r \<in> R"  "?a\<^sub>i \<in> R"  "?b\<^sub>r \<in> R"  "?b\<^sub>i \<in> R"  "?c\<^sub>r \<in> R"  "?c\<^sub>i \<in> R"
    "?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i) \<in> R"  
    "?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r \<in> R"
    "?b\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?b\<^sub>i\<rmu>?c\<^sub>i) \<in> R"
    "?b\<^sub>r\<rmu>?c\<^sub>i \<ra> ?b\<^sub>i\<rmu>?c\<^sub>r \<in> R" 
    using valid_cntxts ring0.Ring_ZF_1_L4  by auto
  with A1 have "a \<cdot> b \<cdot> c = 
    \<langle>(?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i))\<rmu>?c\<^sub>r \<ra> (\<rm>(?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r)\<rmu>?c\<^sub>i),
    (?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i))\<rmu>?c\<^sub>i \<ra> (?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r)\<rmu>?c\<^sub>r\<rangle>"
    using cplx_mul_add_vals by auto
  moreover from A1 T have 
    "\<langle>?a\<^sub>r\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?b\<^sub>i\<rmu>?c\<^sub>i)) \<ra> (\<rm>?a\<^sub>i\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>i \<ra> ?b\<^sub>i\<rmu>?c\<^sub>r)),
    ?a\<^sub>r\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>i \<ra> ?b\<^sub>i\<rmu>?c\<^sub>r) \<ra> ?a\<^sub>i\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?b\<^sub>i\<rmu>?c\<^sub>i))\<rangle> = 
    a \<cdot> (b \<cdot> c)"
    using cplx_mul_add_vals by auto
  moreover from T have
    "?a\<^sub>r\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?b\<^sub>i\<rmu>?c\<^sub>i)) \<ra> (\<rm>?a\<^sub>i\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>i \<ra> ?b\<^sub>i\<rmu>?c\<^sub>r)) =
    (?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i))\<rmu>?c\<^sub>r \<ra> (\<rm>(?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r)\<rmu>?c\<^sub>i)"
    and
    "?a\<^sub>r\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>i \<ra> ?b\<^sub>i\<rmu>?c\<^sub>r) \<ra> ?a\<^sub>i\<rmu>(?b\<^sub>r\<rmu>?c\<^sub>r \<ra> (\<rm>?b\<^sub>i\<rmu>?c\<^sub>i)) =
    (?a\<^sub>r\<rmu>?b\<^sub>r \<ra> (\<rm>?a\<^sub>i\<rmu>?b\<^sub>i))\<rmu>?c\<^sub>i \<ra> (?a\<^sub>r\<rmu>?b\<^sub>i \<ra> ?a\<^sub>i\<rmu>?b\<^sub>r)\<rmu>?c\<^sub>r"
    using valid_cntxts ring0.Ring_ZF_2_L6 by auto
  ultimately show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)"
    by auto
qed

text\<open>Complex $1$ is real. This really means that the pair 
  $\langle 1,0 \rangle$ is on the real axis.\<close>

lemma (in complex0) ax1re: shows "\<one> \<in> \<real>"
  using valid_cntxts ring0.Ring_ZF_1_L2 by simp

text\<open>The imaginary unit is a "square root" of $-1$ (that is, $i^2 +1 =0$). 
\<close>

lemma (in complex0) axi2m1: shows "\<i>\<cdot>\<i> \<ca> \<one> = \<zero>"
  using valid_cntxts ring0.Ring_ZF_1_L2 ring0.Ring_ZF_1_L3
  cplx_mul_add_vals ring0.Ring_ZF_1_L6 group0.group0_2_L6 
  by simp

text\<open>$0$ is the neutral element of complex addition.\<close>

lemma (in complex0) ax0id: assumes "a \<in> \<complex>"
  shows "a \<ca> \<zero> = a"
  using assms cplx_mul_add_vals valid_cntxts 
    ring0.Ring_ZF_1_L2 ring0.Ring_ZF_1_L3
  by auto

text\<open>The imaginary unit is a complex number.\<close>

lemma (in complex0) axicn: shows "\<i> \<in> \<complex>"
  using valid_cntxts ring0.Ring_ZF_1_L2 by auto

text\<open>All complex numbers have additive inverses.\<close>

lemma (in complex0) axnegex: assumes A1: "a \<in> \<complex>"
  shows "\<exists>x\<in>\<complex>. a \<ca> x  = \<zero>"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?a\<^sub>i = "snd(a)"
  let ?x = "\<langle>\<rm>?a\<^sub>r, \<rm>?a\<^sub>i\<rangle>"
  from A1 have T: 
    "?a\<^sub>r \<in> R"   "?a\<^sub>i \<in> R"   "(\<rm>?a\<^sub>r) \<in> R"   "(\<rm>?a\<^sub>r) \<in> R"
    using valid_cntxts ring0.Ring_ZF_1_L3 by auto
  then have "?x \<in> \<complex>" using valid_cntxts ring0.Ring_ZF_1_L3
    by auto
  moreover from A1 T have "a \<ca> ?x = \<zero>"
    using cplx_mul_add_vals valid_cntxts ring0.Ring_ZF_1_L3
    by auto
  ultimately show "\<exists>x\<in>\<complex>. a \<ca> x  = \<zero>"
    by auto
qed

text\<open>A non-zero complex number has a multiplicative inverse.\<close>

lemma (in complex0) axrecex: assumes A1: "a \<in> \<complex>" and A2: "a\<noteq>\<zero>"
  shows "\<exists>x\<in>\<complex>. a\<cdot>x = \<one>"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?a\<^sub>i = "snd(a)"
  let ?m = "?a\<^sub>r\<rmu>?a\<^sub>r \<ra> ?a\<^sub>i\<rmu>?a\<^sub>i"
  from A1 have T1: "?a\<^sub>r \<in> R"   "?a\<^sub>i \<in> R" by auto
  moreover from A1 A2 have "?a\<^sub>r \<noteq> \<zero>\<^sub>R \<or> ?a\<^sub>i \<noteq> \<zero>\<^sub>R" 
    by auto
  ultimately have "\<exists>c\<in>R. ?m\<rmu>c = \<one>\<^sub>R"
    using valid_cntxts field1.OrdField_ZF_1_L10
    by auto
  then obtain c where I: "c\<in>R" and II: "?m\<rmu>c = \<one>\<^sub>R"
    by auto
  let ?x = "\<langle>?a\<^sub>r\<rmu>c, \<rm>?a\<^sub>i\<rmu>c\<rangle>"
  from T1 I have T2: "?a\<^sub>r\<rmu>c \<in> R"  "(\<rm>?a\<^sub>i\<rmu>c) \<in> R"
    using valid_cntxts ring0.Ring_ZF_1_L4 ring0.Ring_ZF_1_L3
    by auto
  then have "?x \<in> \<complex>" by auto
  moreover from A1 T1 T2 I II have "a\<cdot>?x = \<one>"
    using cplx_mul_add_vals valid_cntxts ring0.ring_rearr_3_elemA
    by auto
  ultimately show "\<exists>x\<in>\<complex>. a\<cdot>x = \<one>" by auto
qed

text\<open>Complex $1$ is a right neutral element for multiplication.\<close>

lemma (in complex0) ax1id: assumes A1: "a \<in> \<complex>"
  shows "a\<cdot>\<one> = a"
  using assms valid_cntxts ring0.Ring_ZF_1_L2 cplx_mul_add_vals
    ring0.Ring_ZF_1_L3 ring0.Ring_ZF_1_L6 by auto

text\<open>A formula for sum of (complex) real numbers.\<close>

lemma (in complex0) sum_of_reals: assumes "a\<in>\<real>"  "b\<in>\<real>"
  shows 
  "a \<ca> b = \<langle>fst(a) \<ra> fst(b),\<zero>\<^sub>R\<rangle>"
  using assms valid_cntxts ring0.Ring_ZF_1_L2 cplx_mul_add_vals
    ring0.Ring_ZF_1_L3 by auto
  
text\<open>The sum of real numbers is real.\<close>

lemma (in complex0) axaddrcl: assumes A1: "a\<in>\<real>"  "b\<in>\<real>"
  shows "a \<ca> b \<in> \<real>" 
  using assms sum_of_reals valid_cntxts ring0.Ring_ZF_1_L4
  by auto

text\<open>The formula for the product of (complex) real numbers.\<close>

lemma (in complex0) prod_of_reals: assumes A1: "a\<in>\<real>"  "b\<in>\<real>"
  shows "a \<cdot> b = \<langle>fst(a)\<rmu>fst(b),\<zero>\<^sub>R\<rangle>"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?b\<^sub>r = "fst(b)"
  from A1 have T: 
    "?a\<^sub>r \<in> R" "?b\<^sub>r \<in> R"  "\<zero>\<^sub>R \<in> R"  "?a\<^sub>r\<rmu>?b\<^sub>r \<in> R"
    using valid_cntxts ring0.Ring_ZF_1_L2 ring0.Ring_ZF_1_L4 
    by auto
  with A1 show "a \<cdot> b = \<langle>?a\<^sub>r\<rmu>?b\<^sub>r,\<zero>\<^sub>R\<rangle>"
    using cplx_mul_add_vals valid_cntxts ring0.Ring_ZF_1_L2 
      ring0.Ring_ZF_1_L6 ring0.Ring_ZF_1_L3 by auto
qed

text\<open>The product of (complex) real numbers is real.\<close>

lemma (in complex0) axmulrcl: assumes "a\<in>\<real>"  "b\<in>\<real>"
  shows "a \<cdot> b \<in> \<real>"
  using assms prod_of_reals valid_cntxts ring0.Ring_ZF_1_L4
  by auto

text\<open>The existence of a real negative of a real number.\<close>

lemma (in complex0) axrnegex: assumes A1: "a\<in>\<real>"
  shows "\<exists> x \<in> \<real>. a \<ca> x = \<zero>"
proof -
  let ?a\<^sub>r = "fst(a)"
  let ?x = "\<langle>\<rm>?a\<^sub>r,\<zero>\<^sub>R\<rangle>"
  from A1 have T: 
    "?a\<^sub>r \<in> R"  "(\<rm>?a\<^sub>r) \<in> R"  "\<zero>\<^sub>R \<in> R" 
    using valid_cntxts ring0.Ring_ZF_1_L3 ring0.Ring_ZF_1_L2 
    by auto
  then have "?x\<in> \<real>" by auto
  moreover from A1 T have "a \<ca> ?x = \<zero>"
    using cplx_mul_add_vals valid_cntxts ring0.Ring_ZF_1_L3
    by auto
  ultimately show "\<exists>x\<in>\<real>. a \<ca> x = \<zero>" by auto
qed

text\<open>Each nonzero real number has a real inverse\<close>

lemma (in complex0) axrrecex: 
  assumes A1:  "a \<in> \<real>"   "a \<noteq> \<zero>"
  shows "\<exists>x\<in>\<real>. a \<cdot> x = \<one>"
proof -
  let ?R\<^sub>0 = "R-{\<zero>\<^sub>R}"
  let ?a\<^sub>r = "fst(a)"
  let ?y = "GroupInv(?R\<^sub>0,restrict(M,?R\<^sub>0\<times>?R\<^sub>0))`(?a\<^sub>r)"
  from A1 have T: "\<langle>?y,\<zero>\<^sub>R\<rangle> \<in> \<real>" using valid_cntxts field0.Field_ZF_1_L5
    by auto
  moreover from A1 T have "a \<cdot> \<langle>?y,\<zero>\<^sub>R\<rangle> = \<one>"
    using prod_of_reals valid_cntxts
    field0.Field_ZF_1_L5 field0.Field_ZF_1_L6 by auto
  ultimately show "\<exists> x \<in> \<real>. a \<cdot> x = \<one>" by auto
qed
  
text\<open>Our \<open>\<real>\<close> symbol is the real axis on the complex plane.\<close>

lemma (in complex0) real_means_real_axis: shows "\<real> = ComplexReals(R,A)"
  using ComplexReals_def by auto

text\<open>The \<open>CplxROrder\<close> thing is a relation on the complex reals.
\<close>

lemma (in complex0) cplx_ord_on_cplx_reals:
  shows "CplxROrder(R,A,r) \<subseteq> \<real>\<times>\<real>"
  using ComplexReals_def slice_proj_bij real_means_real_axis
    CplxROrder_def InducedRelation_def by auto

text\<open>The strict version of the complex relation is a 
  relation on complex reals.\<close>

lemma (in complex0) cplx_strict_ord_on_cplx_reals:
  shows "StrictVersion(CplxROrder(R,A,r)) \<subseteq> \<real>\<times>\<real>"
  using cplx_ord_on_cplx_reals strict_ver_rel by simp

text\<open>The \<open>CplxROrder\<close> thing is a relation on the complex reals.
  Here this is formulated as a statement that in \<open>complex0\<close> context
  $a<b$ implies that $a,b$ are complex reals\<close>

lemma (in complex0) strict_cplx_ord_type: assumes "a \<lsr> b"
  shows "a\<in>\<real>"  "b\<in>\<real>"
  using assms CplxROrder_def def_of_strict_ver InducedRelation_def 
    slice_proj_bij ComplexReals_def real_means_real_axis 
  by auto

text\<open>A more readable version of the definition of the strict order
  relation on the real axis. Recall that in the \<open>complex0\<close>
  context $r$ denotes the (non-strict) order relation on the underlying
  model of real numbers.\<close>

lemma (in complex0) def_of_real_axis_order: shows 
  "\<langle>x,\<zero>\<^sub>R\<rangle> \<lsr> \<langle>y,\<zero>\<^sub>R\<rangle> \<longleftrightarrow> \<langle>x,y\<rangle> \<in> r \<and> x\<noteq>y"
proof
  let ?f = "SliceProjection(ComplexReals(R,A))"
  assume A1: "\<langle>x,\<zero>\<^sub>R\<rangle> \<lsr> \<langle>y,\<zero>\<^sub>R\<rangle>"
  then have "\<langle> ?f`\<langle>x,\<zero>\<^sub>R\<rangle>, ?f`\<langle>y,\<zero>\<^sub>R\<rangle> \<rangle> \<in> r \<and> x \<noteq> y"
    using CplxROrder_def def_of_strict_ver def_of_ind_relA
    by simp
  moreover from A1 have "\<langle>x,\<zero>\<^sub>R\<rangle> \<in> \<real>"  "\<langle>y,\<zero>\<^sub>R\<rangle> \<in> \<real>"
    using strict_cplx_ord_type by auto
  ultimately show "\<langle>x,y\<rangle> \<in> r \<and> x\<noteq>y"
    using slice_proj_bij ComplexReals_def by simp
next assume A1: "\<langle>x,y\<rangle> \<in> r \<and> x\<noteq>y"
  let ?f = "SliceProjection(ComplexReals(R,A))"
  have "?f : \<real> \<rightarrow> R"
    using ComplexReals_def slice_proj_bij real_means_real_axis
    by simp
  moreover from A1 have T: "\<langle>x,\<zero>\<^sub>R\<rangle> \<in> \<real>"   "\<langle>y,\<zero>\<^sub>R\<rangle> \<in> \<real>"
    using valid_cntxts ring1.OrdRing_ZF_1_L3 by auto
  moreover from A1 T have "\<langle> ?f`\<langle>x,\<zero>\<^sub>R\<rangle>, ?f`\<langle>y,\<zero>\<^sub>R\<rangle> \<rangle> \<in> r"
    using slice_proj_bij ComplexReals_def by simp
  ultimately have "\<langle> \<langle>x,\<zero>\<^sub>R\<rangle>, \<langle>y,\<zero>\<^sub>R\<rangle> \<rangle> \<in> InducedRelation(?f,r)"
    using def_of_ind_relB by simp
  with A1 show "\<langle>x,\<zero>\<^sub>R\<rangle> \<lsr> \<langle>y,\<zero>\<^sub>R\<rangle>"
    using CplxROrder_def def_of_strict_ver
    by simp
qed

text\<open>The (non strict) order on complex reals is antisymmetric,
  transitive and total.\<close>

lemma (in complex0) cplx_ord_antsym_trans_tot: shows
  "antisym(CplxROrder(R,A,r))"
  "trans(CplxROrder(R,A,r))"
  "CplxROrder(R,A,r) {is total on} \<real>"
proof -
  let ?f = "SliceProjection(ComplexReals(R,A))"
  have "?f \<in> ord_iso(\<real>,CplxROrder(R,A,r),R,r)"
    using ComplexReals_def slice_proj_bij real_means_real_axis 
      bij_is_ord_iso CplxROrder_def by simp
  moreover have "CplxROrder(R,A,r) \<subseteq> \<real>\<times>\<real>"
    using cplx_ord_on_cplx_reals by simp
  moreover have I:
    "antisym(r)"   "r {is total on} R"   "trans(r)"
    using valid_cntxts ring1.OrdRing_ZF_1_L1 IsAnOrdRing_def 
      IsLinOrder_def by auto
  ultimately show 
    "antisym(CplxROrder(R,A,r))"
    "trans(CplxROrder(R,A,r))"
    "CplxROrder(R,A,r) {is total on} \<real>"
    using ord_iso_pres_antsym ord_iso_pres_tot ord_iso_pres_trans
    by auto
qed

text\<open>The trichotomy law for the strict order on the complex 
  reals.\<close>

lemma (in complex0) cplx_strict_ord_trich: 
  assumes "a \<in> \<real>"  "b \<in> \<real>"
  shows "Exactly_1_of_3_holds(a\<lsr>b, a=b, b\<lsr>a)"
  using assms cplx_ord_antsym_trans_tot strict_ans_tot_trich
  by simp

text\<open>The strict order on the complex reals is kind of 
  antisymetric.\<close>

lemma (in complex0) pre_axlttri: assumes A1: "a \<in> \<real>"   "b \<in> \<real>"
  shows "a \<lsr> b \<longleftrightarrow> \<not>(a=b \<or> b \<lsr> a)"
proof -
  from A1 have "Exactly_1_of_3_holds(a\<lsr>b, a=b, b\<lsr>a)"
    by (rule cplx_strict_ord_trich)
  then show "a \<lsr> b \<longleftrightarrow> \<not>(a=b \<or> b \<lsr> a)"
    by (rule Fol1_L8A)
qed

text\<open>The strict order on complex reals is transitive.\<close>

lemma (in complex0) cplx_strict_ord_trans: 
  shows "trans(StrictVersion(CplxROrder(R,A,r)))"
  using cplx_ord_antsym_trans_tot strict_of_transB by simp
  

text\<open>The strict order on complex reals is transitive - the explicit version
  of \<open>cplx_strict_ord_trans\<close>.\<close>

lemma (in complex0) pre_axlttrn: 
  assumes A1: "a \<lsr> b"   "b \<lsr> c"
  shows "a \<lsr> c"
proof -
  let ?s = "StrictVersion(CplxROrder(R,A,r))"
  from A1 have 
    "trans(?s)"   "\<langle>a,b\<rangle> \<in> ?s \<and> \<langle>b,c\<rangle> \<in> ?s"
    using cplx_strict_ord_trans by auto
  then have "\<langle>a,c\<rangle> \<in> ?s" by (rule Fol1_L3)
  then show "a \<lsr> c" by simp
qed
  
text\<open>The strict order on complex reals is preserved by translations.\<close>

lemma (in complex0) pre_axltadd: 
  assumes A1: "a \<lsr> b" and A2: "c \<in> \<real>"
  shows "c\<ca>a \<lsr> c\<ca>b"
proof -
  from A1 have T: "a\<in>\<real>"  "b\<in>\<real>" using strict_cplx_ord_type
    by auto
  with A1 A2 show "c\<ca>a \<lsr> c\<ca>b" 
    using def_of_real_axis_order valid_cntxts 
      group3.group_strict_ord_transl_inv sum_of_reals 
    by auto
qed

text\<open>The set of positive complex reals is closed with respect to 
  multiplication.\<close>

lemma (in complex0) pre_axmulgt0: assumes A1: "\<zero> \<lsr> a"   "\<zero> \<lsr> b"
  shows "\<zero> \<lsr> a\<cdot>b"
proof -
  from A1 have T: "a\<in>\<real>"  "b\<in>\<real>" using strict_cplx_ord_type
    by auto
  with A1 show "\<zero> \<lsr> a\<cdot>b"
    using def_of_real_axis_order valid_cntxts field1.pos_mul_closed
      def_of_real_axis_order prod_of_reals
    by auto
qed

text\<open>The order on complex reals is linear and complete.\<close>

lemma (in complex0) cmplx_reals_ord_lin_compl: shows
  "CplxROrder(R,A,r) {is complete}"
  "IsLinOrder(\<real>,CplxROrder(R,A,r))"
proof -
  have "SliceProjection(\<real>) \<in> bij(\<real>,R)"
    using slice_proj_bij ComplexReals_def real_means_real_axis 
    by simp
  moreover have "r \<subseteq> R\<times>R" using valid_cntxts ring1.OrdRing_ZF_1_L1
    IsAnOrdRing_def by simp
  moreover from R_are_reals have 
    "r {is complete}" and "IsLinOrder(R,r)"
    using IsAmodelOfReals_def valid_cntxts ring1.OrdRing_ZF_1_L1
    IsAnOrdRing_def by auto
  ultimately show 
    "CplxROrder(R,A,r) {is complete}"
    "IsLinOrder(\<real>,CplxROrder(R,A,r))"
    using CplxROrder_def real_means_real_axis ind_rel_pres_compl 
      ind_rel_pres_lin by auto
qed

text\<open>The property of the strict order on complex reals
  that corresponds to completeness.\<close>

lemma (in complex0) pre_axsup: assumes A1: "X \<subseteq> \<real>"   "X \<noteq> 0" and
  A2: "\<exists>x\<in>\<real>. \<forall>y\<in>X. y \<lsr> x"
  shows 
  "\<exists>x\<in>\<real>. (\<forall>y\<in>X. \<not>(x \<lsr> y)) \<and> (\<forall>y\<in>\<real>. (y \<lsr> x \<longrightarrow> (\<exists>z\<in>X. y \<lsr> z)))"
proof -
  let ?s = "StrictVersion(CplxROrder(R,A,r))"
  have 
    "CplxROrder(R,A,r) \<subseteq> \<real>\<times>\<real>"
    "IsLinOrder(\<real>,CplxROrder(R,A,r))"
    "CplxROrder(R,A,r) {is complete}"
    using cplx_ord_on_cplx_reals cmplx_reals_ord_lin_compl
    by auto
  moreover note A1
  moreover have "?s = StrictVersion(CplxROrder(R,A,r))"
    by simp
  moreover from A2 have "\<exists>u\<in>\<real>. \<forall>y\<in>X. \<langle>y,u\<rangle> \<in> ?s"
    by simp
  ultimately have
    "\<exists>x\<in>\<real>. ( \<forall>y\<in>X. \<langle>x,y\<rangle> \<notin> ?s ) \<and> 
    (\<forall>y\<in>\<real>. \<langle>y,x\<rangle> \<in> ?s \<longrightarrow> (\<exists>z\<in>X. \<langle>y,z\<rangle> \<in> ?s))"
    by (rule strict_of_compl)
  then show "(\<exists>x\<in>\<real>. (\<forall>y\<in>X. \<not>(x \<lsr> y)) \<and> 
    (\<forall>y\<in>\<real>. (y \<lsr> x \<longrightarrow> (\<exists>z\<in>X. y \<lsr> z))))"
    by simp
qed
  
end
  

