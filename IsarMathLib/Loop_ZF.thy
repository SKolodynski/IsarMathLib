section \<open> Loops \<close>

theory Loop_ZF imports Quasigroup_ZF

begin

text\<open>This theory specifies the definition and proves basic  properites of loops. 
  Loops are very similar to groups, the only property that is missing is associativity 
  of the operation.\<close>

subsection\<open> Definitions and notation \<close>

text\<open> In this section we define the notions of identity element and left and right inverse. \<close>

text\<open> A loop is a quasigroup with an identity elemen. \<close>

definition "IsAloop(G,A) \<equiv> IsAquasigroup(G,A) \<and> (\<exists>e\<in>G. \<forall>x\<in>G. A`\<langle>e,x\<rangle> = x \<and> A`\<langle>x,e\<rangle> = x)"

text\<open> The neutral element for a binary operation $A:G\times G \rightarrow G $ is defined
  as the only element $e$ of $G$ such that $A\langle x,e\rangle = x$ and $A\langle e,x\rangle = x$
  for all $x\in G$. Note that although the loop definition guarantees the existence of (some) 
  such element(s) at this point we do not know if this element is unique. 
  We can define this notion   h ere but it will become usable only after we prove uniqueness. \<close> 

definition 
 "TheNeutralElement(G,f) \<equiv> 
  ( THE e. e\<in>G \<and> (\<forall> g\<in>G. f`\<langle>e,g\<rangle> = g \<and> f`\<langle>g,e\<rangle> = g))"

text\<open>We will reuse the notation defined in the \<open>quasigroup0\<close> locale, 
  just adding the assumption about the existence of a neutral element and notation for it.\<close>

locale loop0 = quasigroup0 + 
  assumes ex_ident: "\<exists>e\<in>G. \<forall>x\<in>G. e\<cdot>x = x \<and> x\<cdot>e = x"

  fixes neut ("\<one>")
  defines neut_def[simp]: "\<one> \<equiv> TheNeutralElement(G,A)"

text\<open> In the loop context the pair \<open>(G,A)\<close> forms a loop. \<close>

lemma (in loop0) is_loop: shows "IsAloop(G,A)"
  unfolding IsAloop_def using ex_ident qgroupassum by simp

text\<open>The neutral element is unique in the loop. \<close>

lemma (in loop0) neut_uniq_loop: shows 
  "\<exists>!e. e\<in>G \<and> (\<forall>x\<in>G. e\<cdot>x = x \<and> x\<cdot>e = x)"
proof
  from ex_ident show "\<exists>e. e \<in> G \<and> (\<forall>x\<in>G. e \<cdot> x = x \<and> x \<cdot> e = x)" by auto
next
  fix e y 
  assume "e \<in> G \<and> (\<forall>x\<in>G. e \<cdot> x = x \<and> x \<cdot> e = x)"  "y \<in> G \<and> (\<forall>x\<in>G. y \<cdot> x = x \<and> x \<cdot> y = x)"
  then have "e\<cdot>y =y" and "e\<cdot>y = e" by auto
  thus "e=y" by simp
qed

text\<open> The neutral element as defined in the \<open>loop0\<close> locale is indeed neutral. \<close>

lemma (in loop0) neut_props_loop: shows "\<one>\<in>G" and "\<forall>x\<in>G. \<one>\<cdot>x =x \<and> x\<cdot>\<one> = x"
proof -  
  let ?n = "THE e. e\<in>G \<and> (\<forall>x\<in>G. e\<cdot>x = x \<and> x\<cdot>e = x)"
  have "\<one> = TheNeutralElement(G,A)" by simp
  then have "\<one> = ?n" unfolding TheNeutralElement_def by simp
  moreover have "?n\<in>G \<and> (\<forall>x\<in>G. ?n\<cdot>x = x \<and> x\<cdot>?n = x)" using neut_uniq_loop theI
    by simp
  ultimately show "\<one>\<in>G" and "\<forall>x\<in>G. \<one>\<cdot>x = x \<and> x\<cdot>\<one> = x"
    by auto
qed

text\<open>Every element of a loop has unique left and right inverse (which need not be the same). 
  Here we define the left inverse as a function on $G$. \<close>

definition
  "LeftInv(G,A) \<equiv> {\<langle>x,\<Union>{y\<in>G. A`\<langle>y,x\<rangle> = TheNeutralElement(G,A)}\<rangle>. x\<in>G}"

text\<open>Definition of the right inverse as a function on $G$: \<close>

definition
  "RightInv(G,A) \<equiv> {\<langle>x,\<Union>{y\<in>G. A`\<langle>x,y\<rangle> = TheNeutralElement(G,A)}\<rangle>. x\<in>G}"

text\<open>In a loop $G$ right and left inverses are functions on $G$. \<close>

lemma (in loop0) lr_inv_fun: shows "LeftInv(G,A):G\<rightarrow>G" "RightInv(G,A):G\<rightarrow>G"
  unfolding LeftInv_def RightInv_def
  using neut_props_loop lrdiv_props(1,4) ZF1_1_L9 ZF_fun_from_total
  by auto

text\<open>Right and left inverses have desired properties.\<close>

lemma (in loop0) lr_inv_props: assumes "x\<in>G"
  shows 
    "LeftInv(G,A)`(x) \<in> G" "(LeftInv(G,A)`(x))\<cdot>x = \<one>" 
    "RightInv(G,A)`(x) \<in> G" "x\<cdot>(RightInv(G,A)`(x)) = \<one>"
proof -
  from assms show "LeftInv(G,A)`(x) \<in> G" and "RightInv(G,A)`(x) \<in> G"
    using lr_inv_fun apply_funtype by auto
  from assms have "\<exists>!y. y\<in>G \<and> y\<cdot>x = \<one>"
    using neut_props_loop(1) lrdiv_props(1) by simp
  then have "(\<Union>{y\<in>G.  y\<cdot>x = \<one>})\<cdot>x = \<one>"
    by (rule ZF1_1_L9)
  with assms show "(LeftInv(G,A)`(x))\<cdot>x = \<one>" 
    using lr_inv_fun(1) ZF_fun_from_tot_val unfolding LeftInv_def by simp
  from assms have "\<exists>!y. y\<in>G \<and> x\<cdot>y = \<one>"
    using neut_props_loop(1) lrdiv_props(4) by simp
  then have "x\<cdot>(\<Union>{y\<in>G.  x\<cdot>y = \<one>}) = \<one>"
    by (rule ZF1_1_L9)
  with assms show "x\<cdot>(RightInv(G,A)`(x)) = \<one>" 
    using lr_inv_fun(2) ZF_fun_from_tot_val unfolding RightInv_def by simp
qed

end
