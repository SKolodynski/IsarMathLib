(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2022  Slawomir Kolodynski

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

section \<open>Topology 2\<close>

theory Topology_ZF_2 imports Topology_ZF_1 func1 Fol1

begin

text\<open>This theory continues the series on general topology and covers the 
  definition and basic properties of continuous functions. We also introduce the notion of 
  homeomorphism an prove the pasting lemma.\<close>

subsection\<open>Continuous functions.\<close>

text\<open>In this section we define continuous functions and prove that certain 
  conditions are equivalent to a function being continuous.\<close>

text\<open>In standard math we say that a function is contiuous with respect to two
  topologies $\tau_1 ,\tau_2 $ if the inverse image of sets from topology 
  $\tau_2$ are in $\tau_1$. Here we define a predicate that is supposed
  to reflect that definition, with a difference that we don't require in the
  definition that $\tau_1 ,\tau_2 $ are topologies. This means for example that 
  when we define measurable functions, the definition will be the same. 
  
  The notation \<open>f-``(A)\<close> means the inverse image of (a set)
  $A$ with respect to (a function) $f$.
\<close>

definition
  "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f) \<equiv> (\<forall>U\<in>\<tau>\<^sub>2. f-``(U) \<in> \<tau>\<^sub>1)"

text\<open>A trivial example of a continuous function - identity is continuous.\<close>

lemma id_cont: shows "IsContinuous(\<tau>,\<tau>,id(\<Union>\<tau>))"
proof -
  { fix U assume "U\<in>\<tau>"
    then have "id(\<Union>\<tau>)-``(U) = U" using vimage_id_same by auto
    with \<open>U\<in>\<tau>\<close> have "id(\<Union>\<tau>)-``(U) \<in> \<tau>" by simp
  } then show "IsContinuous(\<tau>,\<tau>,id(\<Union>\<tau>))" using IsContinuous_def
    by simp
qed

text\<open>We will work with a pair of topological spaces. The following 
  locale sets up our context that consists of 
  two topologies $\tau_1,\tau_2$ and 
  a continuous function $f: X_1 \rightarrow X_2$, where $X_i$ is defined 
  as $\bigcup\tau_i$ for $i=1,2$. We also define notation \<open>cl\<^sub>1(A)\<close> and
  \<open>cl\<^sub>2(A)\<close> for closure of a set $A$ in topologies $\tau_1$ and $\tau_2$,
  respectively.\<close>

locale two_top_spaces0 =

  fixes \<tau>\<^sub>1
  assumes tau1_is_top: "\<tau>\<^sub>1 {is a topology}"

  fixes \<tau>\<^sub>2
  assumes tau2_is_top: "\<tau>\<^sub>2 {is a topology}"
 
  fixes X\<^sub>1
  defines X1_def [simp]: "X\<^sub>1 \<equiv> \<Union>\<tau>\<^sub>1"
  
  fixes X\<^sub>2
  defines X2_def [simp]: "X\<^sub>2 \<equiv> \<Union>\<tau>\<^sub>2"

  fixes f
  assumes fmapAssum: "f: X\<^sub>1 \<rightarrow> X\<^sub>2"

  fixes isContinuous ("_ {is continuous}" [50] 50)
  defines isContinuous_def [simp]: "g {is continuous} \<equiv> IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,g)"

  fixes cl\<^sub>1
  defines cl1_def [simp]: "cl\<^sub>1(A) \<equiv> Closure(A,\<tau>\<^sub>1)"

  fixes cl\<^sub>2
  defines cl2_def [simp]: "cl\<^sub>2(A) \<equiv> Closure(A,\<tau>\<^sub>2)"


text\<open>First we show that theorems proven in locale \<open>topology0\<close> 
  are valid when applied to topologies $\tau_1$ and $\tau_2$.\<close>

lemma (in two_top_spaces0) topol_cntxs_valid:
  shows "topology0(\<tau>\<^sub>1)" and "topology0(\<tau>\<^sub>2)"
  using tau1_is_top tau2_is_top topology0_def by auto
  
text\<open>For continuous functions the inverse image of a closed set is closed.\<close>

lemma (in two_top_spaces0) TopZF_2_1_L1: 
  assumes A1: "f {is continuous}" and A2: "D {is closed in} \<tau>\<^sub>2"
  shows "f-``(D) {is closed in} \<tau>\<^sub>1"
proof -
  from fmapAssum have  "f-``(D) \<subseteq> X\<^sub>1" using func1_1_L3 by simp
  moreover from fmapAssum have "f-``(X\<^sub>2 - D) =  X\<^sub>1 - f-``(D)" 
    using Pi_iff function_vimage_Diff func1_1_L4 by auto
  ultimately have "X\<^sub>1 - f-``(X\<^sub>2 - D) = f-``(D)" by auto
  moreover from A1 A2 have "(X\<^sub>1 - f-``(X\<^sub>2 - D)) {is closed in} \<tau>\<^sub>1"
    using IsClosed_def IsContinuous_def topol_cntxs_valid topology0.Top_3_L9
    by simp
  ultimately show "f-``(D) {is closed in} \<tau>\<^sub>1" by simp
qed

text\<open>If the inverse image of every closed set is closed, then the
  image of a closure is contained in the closure of the image.\<close>

lemma (in two_top_spaces0) Top_ZF_2_1_L2:
  assumes A1: "\<forall>D. ((D {is closed in} \<tau>\<^sub>2) \<longrightarrow> f-``(D) {is closed in} \<tau>\<^sub>1)"
  and A2: "A \<subseteq> X\<^sub>1"
  shows "f``(cl\<^sub>1(A)) \<subseteq> cl\<^sub>2(f``(A))"
proof -
  from fmapAssum have "f``(A) \<subseteq> cl\<^sub>2(f``(A))"
    using func1_1_L6 topol_cntxs_valid topology0.cl_contains_set 
    by simp
  with fmapAssum have "f-``(f``(A)) \<subseteq> f-``(cl\<^sub>2(f``(A)))"
    by auto
  moreover from fmapAssum A2 have "A \<subseteq> f-``(f``(A))"
    using func1_1_L9 by simp
  ultimately have "A \<subseteq> f-``(cl\<^sub>2(f``(A)))" by auto
  with fmapAssum A1 have "f``(cl\<^sub>1(A)) \<subseteq> f``(f-``(cl\<^sub>2(f``(A))))"
    using func1_1_L6 func1_1_L8 IsClosed_def 
      topol_cntxs_valid topology0.cl_is_closed topology0.Top_3_L13
    by simp
  moreover from fmapAssum have "f``(f-``(cl\<^sub>2(f``(A)))) \<subseteq> cl\<^sub>2(f``(A))"
    using fun_is_function function_image_vimage by simp
  ultimately show "f``(cl\<^sub>1(A)) \<subseteq> cl\<^sub>2(f``(A))"
    by auto
qed
    
text\<open>If $f\left( \overline{A}\right)\subseteq \overline{f(A)}$ 
  (the image of the closure is contained in the closure of the image), then
  $\overline{f^{-1}(B)}\subseteq f^{-1}\left( \overline{B} \right)$ 
  (the inverse image of the closure contains the closure of the 
  inverse image).\<close>

lemma (in two_top_spaces0) Top_ZF_2_1_L3:
  assumes A1: "\<forall> A. ( A \<subseteq> X\<^sub>1 \<longrightarrow> f``(cl\<^sub>1(A)) \<subseteq> cl\<^sub>2(f``(A)))"
  shows "\<forall>B. ( B \<subseteq> X\<^sub>2 \<longrightarrow> cl\<^sub>1(f-``(B)) \<subseteq> f-``(cl\<^sub>2(B)) )"
proof -
  { fix B assume "B \<subseteq> X\<^sub>2"
    from fmapAssum A1 have "f``(cl\<^sub>1(f-``(B))) \<subseteq> cl\<^sub>2(f``(f-``(B)))"
      using func1_1_L3 by simp
    moreover from fmapAssum \<open>B \<subseteq> X\<^sub>2\<close> have "cl\<^sub>2(f``(f-``(B))) \<subseteq> cl\<^sub>2(B)"
      using fun_is_function function_image_vimage func1_1_L6
	topol_cntxs_valid topology0.top_closure_mono
      by simp
    ultimately have "f-``(f``(cl\<^sub>1(f-``(B)))) \<subseteq> f-``(cl\<^sub>2(B))"
      using fmapAssum fun_is_function by auto
    moreover from fmapAssum \<open>B \<subseteq> X\<^sub>2\<close> have 
      "cl\<^sub>1(f-``(B)) \<subseteq> f-``(f``(cl\<^sub>1(f-``(B))))"
      using func1_1_L3 func1_1_L9 IsClosed_def 
	topol_cntxs_valid topology0.cl_is_closed by simp
    ultimately have "cl\<^sub>1(f-``(B)) \<subseteq> f-``(cl\<^sub>2(B))" by auto
  } then show ?thesis by simp
qed

text\<open>If $\overline{f^{-1}(B)}\subseteq f^{-1}\left( \overline{B} \right)$ 
  (the inverse image of a closure contains the closure of the 
  inverse image), then the function is continuous. This lemma closes a series of 
  implications in lemmas  \<open> Top_ZF_2_1_L1\<close>, 
  \<open> Top_ZF_2_1_L2\<close> and \<open> Top_ZF_2_1_L3\<close> showing equivalence 
  of four definitions of continuity.\<close>

lemma (in two_top_spaces0) Top_ZF_2_1_L4:
  assumes A1: "\<forall>B. ( B \<subseteq> X\<^sub>2 \<longrightarrow> cl\<^sub>1(f-``(B)) \<subseteq> f-``(cl\<^sub>2(B)) )"
  shows "f {is continuous}"
proof -
  { fix U assume "U \<in> \<tau>\<^sub>2"
    then have "(X\<^sub>2 - U) {is closed in} \<tau>\<^sub>2"
      using topol_cntxs_valid topology0.Top_3_L9 by simp
    moreover have "X\<^sub>2 - U \<subseteq> \<Union>\<tau>\<^sub>2" by auto
    ultimately have "cl\<^sub>2(X\<^sub>2 - U) = X\<^sub>2 - U" 
      using topol_cntxs_valid topology0.Top_3_L8 by simp
    moreover from A1 have "cl\<^sub>1(f-``(X\<^sub>2 - U)) \<subseteq> f-``(cl\<^sub>2(X\<^sub>2 - U))" 
      by auto
    ultimately have "cl\<^sub>1(f-``(X\<^sub>2 - U)) \<subseteq> f-``(X\<^sub>2 - U)" by simp
    moreover from fmapAssum have "f-``(X\<^sub>2 - U) \<subseteq> cl\<^sub>1(f-``(X\<^sub>2 - U))"
      using func1_1_L3 topol_cntxs_valid topology0.cl_contains_set
      by simp
    ultimately have "f-``(X\<^sub>2 - U) {is closed in} \<tau>\<^sub>1"
      using fmapAssum func1_1_L3 topol_cntxs_valid topology0.Top_3_L8
      by auto
    with fmapAssum have "f-``(U) \<in> \<tau>\<^sub>1" 
      using fun_is_function function_vimage_Diff func1_1_L4
	func1_1_L3 IsClosed_def double_complement by simp
  } then have "\<forall>U\<in>\<tau>\<^sub>2. f-``(U) \<in> \<tau>\<^sub>1" by simp
  then show ?thesis using IsContinuous_def by simp
qed

text\<open>Another condition for continuity: it is sufficient to check if the 
  inverse image of every set in a base is open.\<close>

lemma (in two_top_spaces0) Top_ZF_2_1_L5:
  assumes A1: "B {is a base for} \<tau>\<^sub>2" and A2: "\<forall>U\<in>B. f-``(U) \<in> \<tau>\<^sub>1" 
  shows "f {is continuous}"
proof -
  { fix V assume A3: "V \<in> \<tau>\<^sub>2"
    with A1 obtain A where "A \<subseteq> B"  "V = \<Union>A"
      using IsAbaseFor_def by auto
    with A2 have "{f-``(U). U\<in>A} \<subseteq> \<tau>\<^sub>1" by auto
    with tau1_is_top have "\<Union> {f-``(U). U\<in>A} \<in> \<tau>\<^sub>1"
      using IsATopology_def by simp
    moreover from \<open>A \<subseteq> B\<close> \<open>V = \<Union>A\<close> have "f-``(V) = \<Union>{f-``(U). U\<in>A}" 
      by auto
    ultimately have "f-``(V) \<in>  \<tau>\<^sub>1" by simp
  } then show "f {is continuous}" using IsContinuous_def
    by simp
qed
  
text\<open>We can strenghten the previous lemma: it is sufficient to check if the 
  inverse image of every set in a subbase is open. The proof is rather awkward,
  as usual when we deal with general intersections. We have to keep track of 
  the case when the collection is empty.\<close>

lemma (in two_top_spaces0) Top_ZF_2_1_L6:
  assumes A1: "B {is a subbase for} \<tau>\<^sub>2" and A2: "\<forall>U\<in>B. f-``(U) \<in> \<tau>\<^sub>1" 
  shows "f {is continuous}"
proof -
  let ?C = "{\<Inter>A. A \<in> FinPow(B)}"
  from A1 have "?C {is a base for} \<tau>\<^sub>2"
    using IsAsubBaseFor_def by simp
  moreover have "\<forall>U\<in>?C. f-``(U) \<in> \<tau>\<^sub>1"
  proof
    fix U assume "U\<in>?C"
    { assume "f-``(U) = 0"
      with tau1_is_top have "f-``(U) \<in> \<tau>\<^sub>1"
	using empty_open by simp }
    moreover
    { assume "f-``(U) \<noteq> 0"
      then have "U\<noteq>0" by (rule func1_1_L13)
      moreover from \<open>U\<in>?C\<close> obtain A where 
	"A \<in> FinPow(B)" and "U = \<Inter>A" 
	by auto
      ultimately have "\<Inter>A\<noteq>0" by simp
      then have "A\<noteq>0" by (rule inter_nempty_nempty)
      then have "{f-``(W). W\<in>A} \<noteq> 0" by simp
      moreover from A2 \<open>A \<in> FinPow(B)\<close> have "{f-``(W). W\<in>A} \<in> FinPow(\<tau>\<^sub>1)"
	by (rule fin_image_fin)
      ultimately have "\<Inter>{f-``(W). W\<in>A} \<in> \<tau>\<^sub>1"
	using topol_cntxs_valid topology0.fin_inter_open_open by simp
      moreover
      from \<open>A \<in> FinPow(B)\<close> have "A \<subseteq> B" using FinPow_def by simp
      with tau2_is_top A1 have "A \<subseteq> Pow(X\<^sub>2)"
	using IsAsubBaseFor_def IsATopology_def by auto
      with fmapAssum \<open>A\<noteq>0\<close> \<open>U = \<Inter>A\<close> have "f-``(U) = \<Inter>{f-``(W). W\<in>A}"
	using func1_1_L12 by simp
      ultimately have "f-``(U) \<in> \<tau>\<^sub>1" by simp }
    ultimately show "f-``(U) \<in> \<tau>\<^sub>1" by blast
  qed
  ultimately show "f {is continuous}"
    using Top_ZF_2_1_L5 by simp
qed

text\<open>A dual of \<open> Top_ZF_2_1_L5\<close>: a function that maps base sets to open sets
  is open.\<close>

lemma (in two_top_spaces0) base_image_open: 
  assumes A1: "\<B> {is a base for} \<tau>\<^sub>1" and A2: "\<forall>B\<in>\<B>. f``(B) \<in> \<tau>\<^sub>2" and A3: "U\<in>\<tau>\<^sub>1" 
  shows "f``(U) \<in> \<tau>\<^sub>2"
proof -
  from A1 A3 obtain \<E> where "\<E> \<in> Pow(\<B>)" and "U = \<Union>\<E>" using Top_1_2_L1 by blast
  with A1 have "f``(U) = \<Union>{f``(E). E \<in> \<E>}" using Top_1_2_L5  fmapAssum image_of_Union
    by auto
  moreover 
  from A2 \<open>\<E> \<in> Pow(\<B>)\<close> have "{f``(E). E \<in> \<E>} \<in> Pow(\<tau>\<^sub>2)" by auto
  then have "\<Union>{f``(E). E \<in> \<E>} \<in> \<tau>\<^sub>2" using tau2_is_top IsATopology_def by simp
  ultimately show ?thesis using tau2_is_top IsATopology_def by auto
qed

text\<open>A composition of two continuous functions is continuous.\<close>

lemma comp_cont: assumes "IsContinuous(T,S,f)" and "IsContinuous(S,R,g)"
  shows "IsContinuous(T,R,g O f)"
  using assms IsContinuous_def vimage_comp by simp

text\<open>A composition of three continuous functions is continuous.\<close>

lemma comp_cont3: 
  assumes "IsContinuous(T,S,f)" and "IsContinuous(S,R,g)" and "IsContinuous(R,P,h)"
  shows "IsContinuous(T,P,h O g O f)"
  using assms IsContinuous_def vimage_comp by simp

text\<open>The graph of a continuous function into a Hausdorff topological space is closed
  in the product topology. Recall that in ZF a function is the same as its graph.\<close>

lemma (in two_top_spaces0) into_T2_graph_closed:
  assumes "f {is continuous}" "\<tau>\<^sub>2 {is T\<^sub>2}"
  shows "f {is closed in} ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2)"
proof -
  from fmapAssum have "f = {\<langle>x,f`(x)\<rangle>. x\<in>X\<^sub>1}" using fun_is_set_of_pairs
    by simp
  let ?f\<^sub>c = "X\<^sub>1\<times>X\<^sub>2 - f"
  have "?f\<^sub>c \<in> ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2)"
  proof -
    { fix p assume "p\<in>?f\<^sub>c"
      then have "p \<in> X\<^sub>1\<times>X\<^sub>2" and "p \<notin> f" by auto
      from \<open>p\<in>X\<^sub>1\<times>X\<^sub>2\<close> obtain x y where "x\<in>X\<^sub>1" "y\<in>X\<^sub>2" "p = \<langle>x,y\<rangle>"
        by auto
      have "y\<noteq>f`(x)"
      proof -
        { assume "y=f`(x)"
          with \<open>x\<in>X\<^sub>1\<close> \<open>p = \<langle>x,y\<rangle>\<close> have "p \<in> {\<langle>x,f`(x)\<rangle>. x\<in>X\<^sub>1}" by auto
          with \<open>f = {\<langle>x,f`(x)\<rangle>. x\<in>X\<^sub>1}\<close> \<open>p \<notin> f\<close> have False by auto
        } thus "y\<noteq>f`(x)" by auto
      qed
      from fmapAssum \<open>x\<in>X\<^sub>1\<close> have "f`(x) \<in> X\<^sub>2" by (rule apply_funtype)
      with \<open>y\<in>X\<^sub>2\<close>  have "y\<in>\<Union>\<tau>\<^sub>2" "f`(x) \<in> \<Union>\<tau>\<^sub>2" by auto
      with assms(2) \<open>y\<noteq>f`(x)\<close> obtain U V 
        where "U\<in>\<tau>\<^sub>2" "V\<in>\<tau>\<^sub>2" "y\<in>U" "f`(x)\<in>V" "U\<inter>V = 0"
        unfolding isT2_def by blast
      let ?W = "f-``(V)"
      have "?W\<in>\<tau>\<^sub>1" "?W\<subseteq>X\<^sub>1" "U\<subseteq>X\<^sub>2" "x\<in>?W" "p\<in>?W\<times>U" "f``(?W) \<subseteq> V"
      proof -
        from assms(1) have "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" by simp
        with \<open>V\<in>\<tau>\<^sub>2\<close> \<open>U\<in>\<tau>\<^sub>2\<close> show "?W\<in>\<tau>\<^sub>1" "?W\<subseteq>X\<^sub>1" "U\<subseteq>X\<^sub>2" 
          unfolding IsContinuous_def by auto
        from fmapAssum \<open>x\<in>X\<^sub>1\<close> \<open>f`(x)\<in>V\<close> show "x\<in>?W" using func1_1_L15 
          by auto
        with \<open>y\<in>U\<close> \<open>y\<in>U\<close> \<open>p = \<langle>x,y\<rangle>\<close> show  "p\<in>?W\<times>U" by simp
        from fmapAssum show "f``(?W) \<subseteq> V" 
          using fun_is_fun function_image_vimage by simp 
      qed
      from fmapAssum \<open>U\<inter>V = 0\<close> \<open>?W\<subseteq>X\<^sub>1\<close> \<open>U\<subseteq>X\<^sub>2\<close> have "?W\<times>U \<subseteq> ?f\<^sub>c"
        using vimage_prod_dis_graph by blast 
      with \<open>?W\<in>\<tau>\<^sub>1\<close> \<open>U\<in>\<tau>\<^sub>2\<close> \<open>p\<in>?W\<times>U\<close> have "\<exists>W\<in>\<tau>\<^sub>1.\<exists>U\<in>\<tau>\<^sub>2. p\<in>W\<times>U \<and> W\<times>U \<subseteq> ?f\<^sub>c" 
        by blast
    } 
    with tau1_is_top tau2_is_top show "?f\<^sub>c \<in> ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2)"
      using point_neighb_prod_top by simp    
  qed
  with fmapAssum tau1_is_top tau2_is_top show ?thesis
    using fun_subset_prod Top_1_4_T1(3) unfolding IsClosed_def
    by auto
qed

subsection\<open>Homeomorphisms\<close>

text\<open>This section studies ''homeomorphisms'' - continous bijections whose inverses
  are also continuous. Notions that are preserved by (commute with)
  homeomorphisms are called ''topological invariants''.\<close>

text\<open>Homeomorphism is a bijection that preserves open sets.\<close>

definition "IsAhomeomorphism(T,S,f) \<equiv>
         f \<in> bij(\<Union>T,\<Union>S) \<and> IsContinuous(T,S,f) \<and> IsContinuous(S,T,converse(f))"

text\<open>Inverse (converse) of a homeomorphism is a homeomorphism.\<close>

lemma homeo_inv: assumes "IsAhomeomorphism(T,S,f)"
  shows "IsAhomeomorphism(S,T,converse(f))"
  using assms IsAhomeomorphism_def bij_converse_bij bij_converse_converse
    by auto

text\<open>Homeomorphisms are open maps.\<close>

lemma homeo_open: assumes "IsAhomeomorphism(T,S,f)" and "U\<in>T"
  shows "f``(U) \<in> S"
  using assms image_converse IsAhomeomorphism_def IsContinuous_def by simp

text\<open>A continuous bijection that is an open map is a homeomorphism.\<close>

lemma bij_cont_open_homeo: 
  assumes "f \<in> bij(\<Union>T,\<Union>S)" and "IsContinuous(T,S,f)" and "\<forall>U\<in>T. f``(U) \<in> S" 
  shows "IsAhomeomorphism(T,S,f)"
  using assms image_converse IsAhomeomorphism_def IsContinuous_def by auto

text\<open>A continuous bijection that maps base to open sets is a homeomorphism.\<close>

lemma (in two_top_spaces0) bij_base_open_homeo:
  assumes A1: "f \<in> bij(X\<^sub>1,X\<^sub>2)" and A2: "\<B> {is a base for} \<tau>\<^sub>1"  and A3: "\<C> {is a base for} \<tau>\<^sub>2" and
  A4: "\<forall>U\<in>\<C>. f-``(U) \<in> \<tau>\<^sub>1" and A5: "\<forall>V\<in>\<B>. f``(V) \<in> \<tau>\<^sub>2"
  shows "IsAhomeomorphism(\<tau>\<^sub>1,\<tau>\<^sub>2,f)"
  using assms tau2_is_top tau1_is_top bij_converse_bij bij_is_fun two_top_spaces0_def 
  image_converse two_top_spaces0.Top_ZF_2_1_L5 IsAhomeomorphism_def by simp 

text\<open>A bijection that maps base to base is a homeomorphism.\<close>

lemma (in two_top_spaces0) bij_base_homeo: 
  assumes A1: "f \<in> bij(X\<^sub>1,X\<^sub>2)" and A2: "\<B> {is a base for} \<tau>\<^sub>1" and 
  A3: "{f``(B). B\<in>\<B>} {is a base for} \<tau>\<^sub>2"
  shows "IsAhomeomorphism(\<tau>\<^sub>1,\<tau>\<^sub>2,f)"
proof -
  note A1
  moreover have "f {is continuous}"
  proof -
    { fix C assume "C \<in> {f``(B). B\<in>\<B>}"
      then obtain B where "B\<in>\<B>" and I: "C = f``(B)" by auto
      with A2 have "B \<subseteq> X\<^sub>1" using Top_1_2_L5 by auto
      with A1 A2 \<open>B\<in>\<B>\<close> I have "f-``(C) \<in> \<tau>\<^sub>1" 
         using bij_def inj_vimage_image base_sets_open by auto
    } hence "\<forall>C \<in> {f``(B). B\<in>\<B>}. f-``(C) \<in> \<tau>\<^sub>1" by auto
    with A3 show ?thesis by (rule Top_ZF_2_1_L5)
  qed
  moreover 
  from A3 have "\<forall>B\<in>\<B>. f``(B) \<in> \<tau>\<^sub>2" using base_sets_open by auto
  with A2 have "\<forall>U\<in>\<tau>\<^sub>1. f``(U) \<in> \<tau>\<^sub>2" using base_image_open by simp
  ultimately show ?thesis using bij_cont_open_homeo by simp
qed

text\<open>Interior is a topological invariant.\<close>

theorem int_top_invariant: assumes A1: "A\<subseteq>\<Union>T" and A2: "IsAhomeomorphism(T,S,f)"
  shows "f``(Interior(A,T)) = Interior(f``(A),S)"
proof -
  let ?\<A> = "{U\<in>T. U\<subseteq>A}"
  have I: "{f``(U). U\<in>?\<A>} = {V\<in>S. V \<subseteq> f``(A)}"
  proof
    from A2 show "{f``(U). U\<in>?\<A>} \<subseteq> {V\<in>S. V \<subseteq> f``(A)}"
      using homeo_open by auto
    { fix V assume "V \<in> {V\<in>S. V \<subseteq> f``(A)}"
      hence "V\<in>S" and II: "V \<subseteq> f``(A)" by auto
      let ?U = "f-``(V)"
      from II have "?U \<subseteq> f-``(f``(A))" by auto
      moreover from assms have "f-``(f``(A)) = A"
        using IsAhomeomorphism_def bij_def inj_vimage_image by auto
      moreover from A2 \<open>V\<in>S\<close> have "?U\<in>T" 
        using IsAhomeomorphism_def IsContinuous_def by simp
      moreover 
      from \<open>V\<in>S\<close> have "V \<subseteq> \<Union>S" by auto
      with A2 have "V = f``(?U)" 
        using IsAhomeomorphism_def bij_def surj_image_vimage by auto
      ultimately have "V \<in> {f``(U). U\<in>?\<A>}" by auto
    } thus "{V\<in>S. V \<subseteq> f``(A)} \<subseteq> {f``(U). U\<in>?\<A>}" by auto
  qed
  have "f``(Interior(A,T)) =  f``(\<Union>?\<A>)" unfolding Interior_def by simp
  also from A2 have "\<dots> = \<Union>{f``(U). U\<in>?\<A>}" 
    using IsAhomeomorphism_def bij_def inj_def image_of_Union by auto
  also from I have "\<dots> = Interior(f``(A),S)" unfolding Interior_def by simp
  finally show ?thesis by simp
qed

subsection\<open>Topologies induced by mappings\<close>

text\<open>In this section we consider various ways a topology may be defined on a set that
  is the range (or the domain) of a function whose domain (or range) is a topological space.
\<close>

text\<open>A bijection from a topological space induces a topology on the range.\<close>

theorem bij_induced_top: assumes A1: "T {is a topology}" and A2: "f \<in> bij(\<Union>T,Y)"
  shows 
  "{f``(U). U\<in>T} {is a topology}" and
  "{ {f`(x).x\<in>U}. U\<in>T} {is a topology}" and 
  "(\<Union>{f``(U). U\<in>T}) = Y" and 
  "IsAhomeomorphism(T, {f``(U). U\<in>T},f)"
proof -
  from A2 have "f \<in> inj(\<Union>T,Y)" using bij_def by simp 
  then have "f:\<Union>T\<rightarrow>Y" using inj_def by simp
  let ?S = "{f``(U). U\<in>T}"
  { fix M assume "M \<in> Pow(?S)"
    let ?M\<^sub>T = "{f-``(V). V\<in>M}"
    have "?M\<^sub>T \<subseteq> T"
    proof
      fix W assume "W\<in>?M\<^sub>T"
      then obtain V where "V\<in>M" and I: "W = f-``(V)" by auto
      with \<open>M \<in> Pow(?S)\<close> have "V\<in>?S" by auto
      then obtain U where "U\<in>T" and  "V = f``(U)" by auto
      with I have "W = f-``(f``(U))" by simp
      with \<open>f \<in> inj(\<Union>T,Y)\<close>  \<open>U\<in>T\<close> have "W = U" using inj_vimage_image by blast 
      with \<open>U\<in>T\<close> show "W\<in>T" by simp
    qed
    with A1 have "(\<Union>?M\<^sub>T) \<in> T" using IsATopology_def by simp
    hence "f``(\<Union>?M\<^sub>T) \<in>  ?S" by auto 
    moreover have "f``(\<Union>?M\<^sub>T) = \<Union>M"
    proof -
      from \<open>f:\<Union>T\<rightarrow>Y\<close> \<open>?M\<^sub>T \<subseteq> T\<close>  have "f``(\<Union>?M\<^sub>T) = \<Union>{f``(U). U\<in>?M\<^sub>T}"
         using image_of_Union by auto 
      moreover have "{f``(U). U\<in>?M\<^sub>T} = M"
      proof -
        from \<open>f:\<Union>T\<rightarrow>Y\<close> have "\<forall>U\<in>T. f``(U) \<subseteq> Y" using  func1_1_L6 by simp
        with \<open>M \<in> Pow(?S)\<close> have "M \<subseteq> Pow(Y)" by auto 
        with A2 show "{f``(U). U\<in>?M\<^sub>T} = M" using bij_def surj_subsets by auto
      qed
      ultimately show "f``(\<Union>?M\<^sub>T) = \<Union>M" by simp 
    qed
    ultimately have "\<Union>M \<in> ?S" by auto
  } then have "\<forall>M\<in>Pow(?S). \<Union>M \<in> ?S" by auto
  moreover
  { fix U V assume "U\<in>?S" "V\<in>?S"
    then obtain U\<^sub>T V\<^sub>T where "U\<^sub>T \<in> T"   "V\<^sub>T \<in> T" and 
      I: "U = f``(U\<^sub>T)"  "V = f``(V\<^sub>T)"
      by auto
    with A1 have "U\<^sub>T\<inter>V\<^sub>T \<in> T" using IsATopology_def by simp
    hence "f``(U\<^sub>T\<inter>V\<^sub>T) \<in> ?S" by auto
    moreover have "f``(U\<^sub>T\<inter>V\<^sub>T) = U\<inter>V"
    proof -
      from \<open>U\<^sub>T \<in> T\<close>  \<open>V\<^sub>T \<in> T\<close> have "U\<^sub>T \<subseteq> \<Union>T"  "V\<^sub>T \<subseteq> \<Union>T"
        using bij_def by auto
      with \<open>f \<in> inj(\<Union>T,Y)\<close> I show "f``(U\<^sub>T\<inter>V\<^sub>T) = U\<inter>V" using inj_image_inter 
      by simp 
    qed
    ultimately have "U\<inter>V \<in> ?S" by simp 
  } then have "\<forall>U\<in>?S. \<forall>V\<in>?S. U\<inter>V \<in> ?S" by auto 
  ultimately show "?S {is a topology}" using IsATopology_def by simp
  moreover from \<open>f:\<Union>T\<rightarrow>Y\<close> have "\<forall>U\<in>T. f``(U) = {f`(x).x\<in>U}"
    using func_imagedef by blast
  ultimately show "{ {f`(x).x\<in>U}. U\<in>T} {is a topology}" by simp  
  show "\<Union>?S =  Y"
  proof 
    from \<open>f:\<Union>T\<rightarrow>Y\<close> have "\<forall>U\<in>T. f``(U) \<subseteq> Y" using func1_1_L6 by simp
    thus "\<Union>?S \<subseteq> Y" by auto
    from A1 have "f``(\<Union>T) \<subseteq> \<Union>?S" using IsATopology_def by auto 
    with A2 show "Y \<subseteq> \<Union>?S" using bij_def surj_range_image_domain 
      by auto
  qed
  show "IsAhomeomorphism(T,?S,f)"
  proof -
    from A2  \<open>\<Union>?S =  Y\<close> have "f \<in> bij(\<Union>T,\<Union>?S)" by simp
    moreover have "IsContinuous(T,?S,f)"
    proof -
      { fix V assume "V\<in>?S"
        then obtain U where "U\<in>T" and "V = f``(U)" by auto
        hence "U \<subseteq> \<Union>T" and "f-``(V) = f-``(f``(U))"  by auto
        with \<open>f \<in> inj(\<Union>T,Y)\<close>  \<open>U\<in>T\<close> have "f-``(V) \<in> T"  using inj_vimage_image 
          by simp 
      } then show "IsContinuous(T,?S,f)" unfolding IsContinuous_def by auto
    qed
    ultimately show"IsAhomeomorphism(T,?S,f)" using bij_cont_open_homeo 
      by auto 
  qed
qed

subsection\<open>Partial functions and continuity\<close>

text\<open>Suppose we have two topologies $\tau_1,\tau_2$ on sets
$X_i=\bigcup\tau_i, i=1,2$. Consider some function $f:A\rightarrow X_2$, where
$A\subseteq X_1$ (we will call such function ''partial''). In such situation we have two
natural possibilities for the pairs of topologies with respect to which this function may
be continuous. One is obviously the original $\tau_1,\tau_2$ and in the second one
the first element of the pair is the topology relative to the domain of the
function: $\{A\cap U | U \in \tau_1\}$. These two possibilities are not exactly
the same and the goal of this section is to explore the differences.\<close>

text\<open>If a function is continuous, then its restriction is continous in relative
  topology.\<close>

lemma (in two_top_spaces0) restr_cont:
  assumes A1: "A \<subseteq> X\<^sub>1" and A2: "f {is continuous}"
  shows "IsContinuous(\<tau>\<^sub>1 {restricted to} A, \<tau>\<^sub>2,restrict(f,A))"
proof -
  let ?g = "restrict(f,A)"
  { fix U assume "U \<in> \<tau>\<^sub>2"
    with A2 have "f-``(U) \<in> \<tau>\<^sub>1" using IsContinuous_def by simp
    moreover from A1 have "?g-``(U) = f-``(U) \<inter> A"
      using fmapAssum func1_2_L1 by simp
    ultimately have "?g-``(U) \<in> (\<tau>\<^sub>1 {restricted to} A)"
      using RestrictedTo_def by auto
  } then show ?thesis using IsContinuous_def by simp
qed

text\<open>If a function is continuous, then it is continuous when we restrict
  the topology on the range to the image of the domain.\<close>

lemma (in two_top_spaces0) restr_image_cont:
  assumes A1: "f {is continuous}"
  shows "IsContinuous(\<tau>\<^sub>1, \<tau>\<^sub>2 {restricted to} f``(X\<^sub>1),f)"
proof -
  have "\<forall>U \<in> \<tau>\<^sub>2 {restricted to} f``(X\<^sub>1). f-``(U) \<in> \<tau>\<^sub>1"
  proof
    fix U assume "U \<in> \<tau>\<^sub>2 {restricted to} f``(X\<^sub>1)"
    then obtain V where "V \<in> \<tau>\<^sub>2" and "U = V \<inter> f``(X\<^sub>1)"
      using RestrictedTo_def by auto
    with A1 show  "f-``(U) \<in> \<tau>\<^sub>1"
      using fmapAssum inv_im_inter_im IsContinuous_def
      by simp
  qed
  then show ?thesis using IsContinuous_def by simp
qed

text\<open>A combination of \<open>restr_cont\<close> and \<open>restr_image_cont\<close>.\<close>

lemma (in two_top_spaces0) restr_restr_image_cont:
  assumes A1: "A \<subseteq> X\<^sub>1" and A2: "f {is continuous}" and
  A3: "g = restrict(f,A)" and
  A4: "\<tau>\<^sub>3 = \<tau>\<^sub>1 {restricted to} A"
  shows "IsContinuous(\<tau>\<^sub>3, \<tau>\<^sub>2 {restricted to} g``(A),g)"
proof -
  from A1 A4 have "\<Union>\<tau>\<^sub>3 = A"
    using union_restrict by auto
  have "two_top_spaces0(\<tau>\<^sub>3, \<tau>\<^sub>2, g)"
  proof -
    from A4 have
      "\<tau>\<^sub>3 {is a topology}" and "\<tau>\<^sub>2 {is a topology}"
      using tau1_is_top tau2_is_top
	topology0_def topology0.Top_1_L4 by auto
    moreover from A1 A3 \<open>\<Union>\<tau>\<^sub>3 = A\<close> have "g: \<Union>\<tau>\<^sub>3 \<rightarrow> \<Union>\<tau>\<^sub>2"
      using fmapAssum restrict_type2 by simp
    ultimately show ?thesis using two_top_spaces0_def
      by simp
  qed
  moreover from assms have "IsContinuous(\<tau>\<^sub>3, \<tau>\<^sub>2, g)"
    using restr_cont by simp
  ultimately have "IsContinuous(\<tau>\<^sub>3, \<tau>\<^sub>2 {restricted to} g``(\<Union>\<tau>\<^sub>3),g)"
    by (rule two_top_spaces0.restr_image_cont)
  moreover note \<open>\<Union>\<tau>\<^sub>3 = A\<close>
  ultimately show ?thesis by simp
qed

text\<open>We need a context similar to \<open>two_top_spaces0\<close> but without
the global function $f:X_1\rightarrow X_2$.\<close>

locale two_top_spaces1 =

  fixes \<tau>\<^sub>1
  assumes tau1_is_top: "\<tau>\<^sub>1 {is a topology}"

  fixes \<tau>\<^sub>2
  assumes tau2_is_top: "\<tau>\<^sub>2 {is a topology}"

  fixes X\<^sub>1
  defines X1_def [simp]: "X\<^sub>1 \<equiv> \<Union>\<tau>\<^sub>1"

  fixes X\<^sub>2
  defines X2_def [simp]: "X\<^sub>2 \<equiv> \<Union>\<tau>\<^sub>2"

text\<open>If a partial function $g:X_1\supseteq A\rightarrow X_2$ is continuous with
respect to $(\tau_1,\tau_2)$, then $A$ is open (in $\tau_1$) and 
the function is continuous in the relative topology.\<close>

lemma (in two_top_spaces1) partial_fun_cont:
  assumes A1: "g:A\<rightarrow>X\<^sub>2" and A2: "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,g)"
  shows "A \<in> \<tau>\<^sub>1" and "IsContinuous(\<tau>\<^sub>1 {restricted to} A, \<tau>\<^sub>2, g)"
proof -
  from A2 have "g-``(X\<^sub>2) \<in> \<tau>\<^sub>1" 
    using tau2_is_top IsATopology_def IsContinuous_def by simp
  with A1 show "A \<in> \<tau>\<^sub>1" using func1_1_L4 by simp
  { fix V assume "V \<in> \<tau>\<^sub>2"
    with A2 have "g-``(V) \<in> \<tau>\<^sub>1" using IsContinuous_def by simp
    moreover
    from A1 have "g-``(V) \<subseteq> A" using func1_1_L3 by simp
    hence "g-``(V) = A \<inter> g-``(V)" by auto
    ultimately have "g-``(V) \<in> (\<tau>\<^sub>1 {restricted to} A)"
      using RestrictedTo_def by auto
  } then show "IsContinuous(\<tau>\<^sub>1 {restricted to} A, \<tau>\<^sub>2, g)"
    using IsContinuous_def by simp
qed

text\<open>For partial function defined on open sets continuity in the whole
  and relative topologies are the same.\<close>

lemma (in two_top_spaces1) part_fun_on_open_cont:
  assumes A1: "g:A\<rightarrow>X\<^sub>2" and A2: "A \<in> \<tau>\<^sub>1"
  shows "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,g) \<longleftrightarrow> 
         IsContinuous(\<tau>\<^sub>1 {restricted to} A, \<tau>\<^sub>2, g)"
proof
  assume "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,g)"
  with A1 show "IsContinuous(\<tau>\<^sub>1 {restricted to} A, \<tau>\<^sub>2, g)"
    using partial_fun_cont by simp
  next
    assume I: "IsContinuous(\<tau>\<^sub>1 {restricted to} A, \<tau>\<^sub>2, g)"
    { fix V assume "V \<in> \<tau>\<^sub>2"
      with I have "g-``(V) \<in> (\<tau>\<^sub>1 {restricted to} A)"
        using IsContinuous_def by simp
      then obtain W where "W \<in> \<tau>\<^sub>1" and "g-``(V) = A\<inter>W"
        using RestrictedTo_def by auto
      with A2 have "g-``(V) \<in> \<tau>\<^sub>1" using tau1_is_top IsATopology_def 
        by simp
    } then show "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,g)" using IsContinuous_def
      by simp
qed

subsection\<open>Product topology and continuity\<close>

text\<open>We start with three topological spaces $(\tau_1,X_1), (\tau_2,X_2)$ and
$(\tau_3,X_3)$ and a function $f:X_1\times X_2\rightarrow X_3$. We will study
the properties of $f$ with respect to the product topology $\tau_1\times \tau_2$
and $\tau_3$. This situation is similar as in locale \<open>two_top_spaces0\<close>
but the first topological space is assumed to be a product of two topological spaces.
\<close>

text\<open>First we define a locale with three topological spaces.\<close>

locale prod_top_spaces0 =

  fixes \<tau>\<^sub>1
  assumes tau1_is_top: "\<tau>\<^sub>1 {is a topology}"

  fixes \<tau>\<^sub>2
  assumes tau2_is_top: "\<tau>\<^sub>2 {is a topology}"

  fixes \<tau>\<^sub>3
  assumes tau3_is_top: "\<tau>\<^sub>3 {is a topology}"

  fixes X\<^sub>1
  defines X1_def [simp]: "X\<^sub>1 \<equiv> \<Union>\<tau>\<^sub>1"

  fixes X\<^sub>2
  defines X2_def [simp]: "X\<^sub>2 \<equiv> \<Union>\<tau>\<^sub>2"

  fixes X\<^sub>3
  defines X3_def [simp]: "X\<^sub>3 \<equiv> \<Union>\<tau>\<^sub>3"

  fixes \<eta>
  defines eta_def [simp]: "\<eta> \<equiv> ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2)"

text\<open>Fixing the first variable in a two-variable continuous function results in a 
continuous function.\<close>

lemma (in prod_top_spaces0) fix_1st_var_cont: 
  assumes "f: X\<^sub>1\<times>X\<^sub>2\<rightarrow>X\<^sub>3" and "IsContinuous(\<eta>,\<tau>\<^sub>3,f)"
  and "x\<in>X\<^sub>1"
  shows "IsContinuous(\<tau>\<^sub>2,\<tau>\<^sub>3,Fix1stVar(f,x))"
  using assms fix_1st_var_vimage IsContinuous_def tau1_is_top tau2_is_top
    prod_sec_open1 by simp

text\<open>Fixing the second variable in a two-variable continuous function results in a
continuous function.\<close>

lemma (in prod_top_spaces0) fix_2nd_var_cont: 
  assumes "f: X\<^sub>1\<times>X\<^sub>2\<rightarrow>X\<^sub>3" and "IsContinuous(\<eta>,\<tau>\<^sub>3,f)"
  and "y\<in>X\<^sub>2"
  shows "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>3,Fix2ndVar(f,y))"
  using assms fix_2nd_var_vimage IsContinuous_def tau1_is_top tau2_is_top
    prod_sec_open2 by simp

text\<open>Having two constinuous mappings we can construct a third one on the cartesian product
  of the domains.\<close>

lemma cart_prod_cont: 
  assumes A1: "\<tau>\<^sub>1 {is a topology}" "\<tau>\<^sub>2 {is a topology}" and 
  A2: "\<eta>\<^sub>1 {is a topology}" "\<eta>\<^sub>2 {is a topology}" and
  A3a: "f\<^sub>1:\<Union>\<tau>\<^sub>1\<rightarrow>\<Union>\<eta>\<^sub>1"  and A3b: "f\<^sub>2:\<Union>\<tau>\<^sub>2\<rightarrow>\<Union>\<eta>\<^sub>2" and
  A4: "IsContinuous(\<tau>\<^sub>1,\<eta>\<^sub>1,f\<^sub>1)" "IsContinuous(\<tau>\<^sub>2,\<eta>\<^sub>2,f\<^sub>2)" and
  A5: "g = {\<langle>p,\<langle>f\<^sub>1`(fst(p)),f\<^sub>2`(snd(p))\<rangle>\<rangle>. p \<in> \<Union>\<tau>\<^sub>1\<times>\<Union>\<tau>\<^sub>2}"
  shows "IsContinuous(ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2),ProductTopology(\<eta>\<^sub>1,\<eta>\<^sub>2),g)"
proof -
  let ?\<tau> = "ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2)"
  let ?\<eta> = "ProductTopology(\<eta>\<^sub>1,\<eta>\<^sub>2)"
  let ?X\<^sub>1 = "\<Union>\<tau>\<^sub>1"
  let ?X\<^sub>2 = "\<Union>\<tau>\<^sub>2"
  let ?Y\<^sub>1 = "\<Union>\<eta>\<^sub>1"
  let ?Y\<^sub>2 = "\<Union>\<eta>\<^sub>2"
  let ?B = "ProductCollection(\<eta>\<^sub>1,\<eta>\<^sub>2)"
  from A1 A2 have "?\<tau> {is a topology}" and "?\<eta> {is a topology}"
    using Top_1_4_T1 by auto
  moreover have "g: ?X\<^sub>1\<times>?X\<^sub>2 \<rightarrow> ?Y\<^sub>1\<times>?Y\<^sub>2"
  proof -
    { fix p assume "p \<in> ?X\<^sub>1\<times>?X\<^sub>2"
      hence "fst(p) \<in> ?X\<^sub>1" and "snd(p) \<in> ?X\<^sub>2" by auto
      from A3a \<open>fst(p) \<in> ?X\<^sub>1\<close> have "f\<^sub>1`(fst(p)) \<in> ?Y\<^sub>1" 
        by (rule apply_funtype)
      moreover from A3b \<open>snd(p) \<in> ?X\<^sub>2\<close> have "f\<^sub>2`(snd(p)) \<in> ?Y\<^sub>2" 
        by (rule apply_funtype)
      ultimately have "\<langle>f\<^sub>1`(fst(p)),f\<^sub>2`(snd(p))\<rangle> \<in> \<Union>\<eta>\<^sub>1\<times>\<Union>\<eta>\<^sub>2" by auto
    } hence "\<forall>p \<in> ?X\<^sub>1\<times>?X\<^sub>2. \<langle>f\<^sub>1`(fst(p)),f\<^sub>2`(snd(p))\<rangle> \<in> ?Y\<^sub>1\<times>?Y\<^sub>2"
      by simp
    with A5 show "g: ?X\<^sub>1\<times>?X\<^sub>2 \<rightarrow> ?Y\<^sub>1\<times>?Y\<^sub>2" using ZF_fun_from_total
      by simp 
  qed
  moreover from A1 A2 have "\<Union>?\<tau> = ?X\<^sub>1\<times>?X\<^sub>2" and "\<Union>?\<eta> = ?Y\<^sub>1\<times>?Y\<^sub>2"
    using Top_1_4_T1 by auto 
  ultimately have "two_top_spaces0(?\<tau>,?\<eta>,g)" using two_top_spaces0_def
    by simp
  moreover from A2 have "?B {is a base for} ?\<eta>" using Top_1_4_T1
    by simp
  moreover have "\<forall>U\<in>?B. g-``(U) \<in> ?\<tau>"
  proof
    fix U assume "U\<in>?B"
    then obtain V W where "V \<in> \<eta>\<^sub>1" "W \<in> \<eta>\<^sub>2" and "U = V\<times>W"
      using ProductCollection_def by auto
    with A3a A3b A5 have "g-``(U) = f\<^sub>1-``(V) \<times> f\<^sub>2-``(W)"
      using cart_prod_fun_vimage by simp
    moreover from A1 A4 \<open>V \<in> \<eta>\<^sub>1\<close> \<open>W \<in> \<eta>\<^sub>2\<close> have "f\<^sub>1-``(V) \<times> f\<^sub>2-``(W) \<in> ?\<tau>"
      using IsContinuous_def prod_open_open_prod by simp 
    ultimately show "g-``(U) \<in> ?\<tau>" by simp 
  qed
  ultimately show ?thesis using two_top_spaces0.Top_ZF_2_1_L5
    by simp
qed

text\<open>A reformulation of the \<open>cart_prod_cont\<close> lemma above in slightly different notation.\<close>

theorem (in two_top_spaces0) product_cont_functions:
  assumes "f:X\<^sub>1\<rightarrow>X\<^sub>2" "g:\<Union>\<tau>\<^sub>3\<rightarrow>\<Union>\<tau>\<^sub>4" 
    "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "IsContinuous(\<tau>\<^sub>3,\<tau>\<^sub>4,g)"
    "\<tau>\<^sub>4{is a topology}" "\<tau>\<^sub>3{is a topology}"
  shows "IsContinuous(ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>3),ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>4),{\<langle>\<langle>x,y\<rangle>,\<langle>f`x,g`y\<rangle>\<rangle>. \<langle>x,y\<rangle>\<in>X\<^sub>1\<times>\<Union>\<tau>\<^sub>3})"
proof -
  have "{\<langle>\<langle>x,y\<rangle>,\<langle>f`x,g`y\<rangle>\<rangle>. \<langle>x,y\<rangle>\<in>X\<^sub>1\<times>\<Union>\<tau>\<^sub>3} = {\<langle>p,\<langle>f`(fst(p)),g`(snd(p))\<rangle>\<rangle>. p \<in> X\<^sub>1\<times>\<Union>\<tau>\<^sub>3}"
    by force
  with tau1_is_top tau2_is_top assms show ?thesis using cart_prod_cont by simp
qed

text\<open>A special case of \<open>cart_prod_cont\<close> when the function acting on the second 
  axis is the identity.\<close>

lemma cart_prod_cont1:
 assumes A1: "\<tau>\<^sub>1 {is a topology}" and A1a: "\<tau>\<^sub>2 {is a topology}" and 
  A2: "\<eta>\<^sub>1 {is a topology}"  and
  A3: "f\<^sub>1:\<Union>\<tau>\<^sub>1\<rightarrow>\<Union>\<eta>\<^sub>1" and A4: "IsContinuous(\<tau>\<^sub>1,\<eta>\<^sub>1,f\<^sub>1)" and
  A5: "g = {\<langle>p, \<langle>f\<^sub>1`(fst(p)),snd(p)\<rangle>\<rangle>. p \<in> \<Union>\<tau>\<^sub>1\<times>\<Union>\<tau>\<^sub>2}"
  shows "IsContinuous(ProductTopology(\<tau>\<^sub>1,\<tau>\<^sub>2),ProductTopology(\<eta>\<^sub>1,\<tau>\<^sub>2),g)"
proof -
  let ?f\<^sub>2 = "id(\<Union>\<tau>\<^sub>2)"
  have "\<forall>x\<in>\<Union>\<tau>\<^sub>2. ?f\<^sub>2`(x) = x" using id_conv by blast
  hence I: "\<forall>p \<in> \<Union>\<tau>\<^sub>1\<times>\<Union>\<tau>\<^sub>2. snd(p) = ?f\<^sub>2`(snd(p))" by simp
  note A1 A1a A2 A1a A3
  moreover have "?f\<^sub>2:\<Union>\<tau>\<^sub>2\<rightarrow>\<Union>\<tau>\<^sub>2"  using id_type by simp
  moreover note A4
  moreover have "IsContinuous(\<tau>\<^sub>2,\<tau>\<^sub>2,?f\<^sub>2)" using id_cont by simp
  moreover have "g = {\<langle>p, \<langle>f\<^sub>1`(fst(p)),?f\<^sub>2`(snd(p))\<rangle> \<rangle>. p \<in> \<Union>\<tau>\<^sub>1\<times>\<Union>\<tau>\<^sub>2}"
  proof
    from A5 I show  "g \<subseteq> {\<langle>p, \<langle>f\<^sub>1`(fst(p)),?f\<^sub>2`(snd(p))\<rangle>\<rangle>. p \<in> \<Union>\<tau>\<^sub>1\<times>\<Union>\<tau>\<^sub>2}"
      by auto
    from A5 I show "{\<langle>p, \<langle>f\<^sub>1`(fst(p)),?f\<^sub>2`(snd(p))\<rangle>\<rangle>. p \<in> \<Union>\<tau>\<^sub>1\<times>\<Union>\<tau>\<^sub>2} \<subseteq> g"
      by auto
  qed
  ultimately show ?thesis by (rule cart_prod_cont)
qed

text\<open>Having two continuous mappings $f,g$ we can construct a third one with values
  in the cartesian product of the codomains of $f,g$, 
  defined by $x\mapsto \langle f(x),g(x) \rangle$. \<close>

lemma (in prod_top_spaces0) cont_funcs_prod: 
  assumes "f:X\<^sub>1\<rightarrow>X\<^sub>2" "g:X\<^sub>1\<rightarrow>X\<^sub>3" "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>3,g)"
  defines "h \<equiv> {\<langle>x,\<langle>f`(x),g`(x)\<rangle>\<rangle>. x\<in>X\<^sub>1}"
  shows "IsContinuous(\<tau>\<^sub>1,ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>3),h)"
proof -
  let ?B = "ProductCollection(\<tau>\<^sub>2,\<tau>\<^sub>3)"
  have 
    "two_top_spaces0(\<tau>\<^sub>1,ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>3),h)"
    "?B {is a base for} ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>3)"
     "\<forall>W\<in>?B. h-``(W) \<in> \<tau>\<^sub>1"
  proof -
    from tau1_is_top tau2_is_top tau3_is_top assms(1,2,5)
      show "two_top_spaces0(\<tau>\<^sub>1,ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>3),h)"
        using vimage_prod Top_1_4_T1(1,3) unfolding two_top_spaces0_def 
        by simp
    from tau2_is_top tau3_is_top show"?B {is a base for} ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>3)"
      using Top_1_4_T1(2) by simp
    from tau1_is_top assms show "\<forall>W\<in>?B. h-``(W) \<in> \<tau>\<^sub>1"
      unfolding ProductCollection_def IsContinuous_def IsATopology_def
      using vimage_prod by simp
  qed
  then show ?thesis by (rule two_top_spaces0.Top_ZF_2_1_L5)
qed

text\<open>Two continuous functions into a Hausdorff space are equal on a closed set.
  Note that in the lemma below $f$ is assumed to map $X_1$ to $X_2$ in the locale, we only
  need to add a similar assumption for the second function. \<close>

lemma (in two_top_spaces0) two_fun_eq_closed:
  assumes "g:X\<^sub>1\<rightarrow>X\<^sub>2" "f {is continuous}" "g {is continuous}"  "\<tau>\<^sub>2 {is T\<^sub>2}"
  shows "{x\<in>X\<^sub>1. f`(x)=g`(x)} {is closed in} \<tau>\<^sub>1"
proof -
  let ?D = "{x\<in>X\<^sub>1. f`(x)=g`(x)}"
  let ?h = "{\<langle>x,\<langle>f`(x),g`(x)\<rangle>\<rangle>. x\<in>X\<^sub>1}"
  have "?h-``({\<langle>y,y\<rangle>. y\<in>X\<^sub>2}) {is closed in} \<tau>\<^sub>1"
    proof -
      have "two_top_spaces0(\<tau>\<^sub>1,ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>2),?h)"
      proof
        from tau1_is_top tau2_is_top
        show "\<tau>\<^sub>1 {is a topology}" and "ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>2) {is a topology}"
          using Top_1_4_T1(1) by auto
        from tau1_is_top tau2_is_top fmapAssum assms(1)
        show "?h : \<Union>\<tau>\<^sub>1 \<rightarrow> \<Union>ProductTopology(\<tau>\<^sub>2, \<tau>\<^sub>2)"
          using vimage_prod(1) Top_1_4_T1(3) by simp
      qed
      moreover 
      have "IsContinuous(\<tau>\<^sub>1,ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>2),?h)"
      proof -
        from tau1_is_top tau2_is_top have "prod_top_spaces0(\<tau>\<^sub>1,\<tau>\<^sub>2,\<tau>\<^sub>2)"
          unfolding prod_top_spaces0_def by simp
        with fmapAssum assms(1,2,3) show ?thesis
          using prod_top_spaces0.cont_funcs_prod by simp 
      qed
      moreover 
      from tau2_is_top assms(4) 
        have "{\<langle>y,y\<rangle>. y\<in>X\<^sub>2} {is closed in} ProductTopology(\<tau>\<^sub>2,\<tau>\<^sub>2)"
          using t2_iff_diag_closed by simp 
      ultimately show ?thesis using two_top_spaces0.TopZF_2_1_L1 
        by simp
    qed 
  with fmapAssum assms(1) show ?thesis using vimage_prod(4)
    by simp
qed

subsection\<open>Pasting lemma\<close>

text\<open>The classical pasting lemma states that if $U_1,U_2$ are both open (or closed) and a function
  is continuous when restricted to both $U_1$ and $U_2$ then it is continuous
  when restricted to $U_1 \cup U_2$. In this section we prove a generalization statement
stating that the set $\{ U \in \tau_1 | f|_U$ is continuous $\}$ is a
topology.\<close>

text\<open>A typical statement of the pasting lemma uses the notion of a function 
restricted to a set being continuous without specifying the topologies with 
respect to which this continuity holds.
In \<open>two_top_spaces0\<close> context the notation \<open>g {is continuous}\<close>
means continuity wth respect to topologies $\tau_1, \tau_2$.
The next lemma is a special case of \<open>partial_fun_cont\<close> and states that if
for some set $A\subseteq X_1=\bigcup \tau_1$
the function $f|_A$ is continuous (with respect to $(\tau_1, \tau_2)$), then 
$A$ has to be open. This clears up terminology and indicates why we need
to pay attention to the issue of which topologies we talk about when we say
that the restricted (to some closed set for example) function is continuos.
\<close>

lemma (in two_top_spaces0) restriction_continuous1:
  assumes A1: "A \<subseteq> X\<^sub>1" and A2: "restrict(f,A) {is continuous}"
  shows "A \<in> \<tau>\<^sub>1"
proof -
  from assms have "two_top_spaces1(\<tau>\<^sub>1,\<tau>\<^sub>2)" and
    "restrict(f,A):A\<rightarrow>X\<^sub>2" and "restrict(f,A) {is continuous}"
    using tau1_is_top tau2_is_top two_top_spaces1_def fmapAssum restrict_fun
      by auto
  then show ?thesis using two_top_spaces1.partial_fun_cont by simp
qed

text\<open>If a fuction is continuous on each set of a collection of open sets, then
  it is continuous on the union of them. We could use continuity with respect to
  the relative topology here, but we know that on open sets this is the same as the
  original topology.\<close>

lemma (in two_top_spaces0) pasting_lemma1:
  assumes A1: "M \<subseteq> \<tau>\<^sub>1" and A2: "\<forall>U\<in>M. restrict(f,U)  {is continuous}"
  shows "restrict(f,\<Union>M) {is continuous}"
proof -
  { fix V assume "V\<in>\<tau>\<^sub>2"
    from A1 have "\<Union>M \<subseteq> X\<^sub>1" by auto
    then have "restrict(f,\<Union>M)-``(V) = f-``(V) \<inter> (\<Union>M)"
      using func1_2_L1 fmapAssum by simp
    also have "\<dots> = \<Union> {f-``(V) \<inter> U. U\<in>M}" by auto
    finally have "restrict(f,\<Union>M)-``(V) = \<Union> {f-``(V) \<inter> U. U\<in>M}" by simp
    moreover
    have "{f-``(V) \<inter> U. U\<in>M} \<in> Pow(\<tau>\<^sub>1)"
    proof -
      { fix W assume "W \<in> {f-``(V) \<inter> U. U\<in>M}"
        then obtain U where "U\<in>M" and I: "W = f-``(V) \<inter> U" by auto
        with A2 have "restrict(f,U) {is continuous}" by simp
        with \<open>V\<in>\<tau>\<^sub>2\<close> have "restrict(f,U)-``(V) \<in> \<tau>\<^sub>1"
          using IsContinuous_def by simp
        moreover from \<open>\<Union>M \<subseteq> X\<^sub>1\<close> and \<open>U\<in>M\<close> 
        have "restrict(f,U)-``(V) = f-``(V) \<inter> U"
          using fmapAssum func1_2_L1 by blast
        ultimately have "f-``(V) \<inter> U \<in> \<tau>\<^sub>1" by simp
        with I have "W \<in> \<tau>\<^sub>1" by simp
      } then show ?thesis by auto
    qed
    then have  "\<Union>{f-``(V) \<inter> U. U\<in>M} \<in> \<tau>\<^sub>1"
       using tau1_is_top IsATopology_def by auto
    ultimately have "restrict(f,\<Union>M)-``(V) \<in> \<tau>\<^sub>1"
      by simp
  } then show ?thesis using IsContinuous_def by simp
qed

text\<open>If a function is continuous on two sets, then it is continuous
  on intersection.\<close>

lemma (in two_top_spaces0) cont_inter_cont:
  assumes A1: "A \<subseteq> X\<^sub>1" "B \<subseteq> X\<^sub>1" and
  A2: "restrict(f,A)  {is continuous}"  "restrict(f,B)  {is continuous}"
  shows "restrict(f,A\<inter>B)  {is continuous}"
proof -
  { fix V assume "V\<in>\<tau>\<^sub>2"
    with assms have
      "restrict(f,A)-``(V) = f-``(V) \<inter> A"  "restrict(f,B)-``(V) = f-``(V) \<inter> B" and
      "restrict(f,A)-``(V) \<in> \<tau>\<^sub>1" and "restrict(f,B)-``(V) \<in> \<tau>\<^sub>1"
        using func1_2_L1 fmapAssum IsContinuous_def by auto
    then have "(restrict(f,A)-``(V)) \<inter> (restrict(f,B)-``(V)) = f-``(V) \<inter> (A\<inter>B)"
      by auto
    moreover 
    from A2 \<open>V\<in>\<tau>\<^sub>2\<close> have 
      "restrict(f,A)-``(V) \<in> \<tau>\<^sub>1" and "restrict(f,B)-``(V) \<in> \<tau>\<^sub>1"
      using IsContinuous_def by auto
    then have "(restrict(f,A)-``(V)) \<inter> (restrict(f,B)-``(V)) \<in> \<tau>\<^sub>1"
      using tau1_is_top IsATopology_def by simp
    moreover 
    from A1 have "(A\<inter>B) \<subseteq> X\<^sub>1" by auto
    then have "restrict(f,A\<inter>B)-``(V) = f-``(V) \<inter> (A\<inter>B)"
      using func1_2_L1 fmapAssum by simp
  ultimately have "restrict(f,A\<inter>B)-``(V) \<in> \<tau>\<^sub>1" by simp
  } then show ?thesis using  IsContinuous_def by auto
qed

text\<open>The collection of open sets $U$ such that $f$ restricted to 
$U$ is continuous, is a topology.\<close>

theorem (in two_top_spaces0) pasting_theorem:
  shows "{U \<in> \<tau>\<^sub>1. restrict(f,U) {is continuous}} {is a topology}"
proof -
  let ?T = "{U \<in> \<tau>\<^sub>1. restrict(f,U) {is continuous}}"
  have "\<forall>M\<in>Pow(?T). \<Union>M \<in> ?T" 
  proof
    fix M assume "M \<in> Pow(?T)"
    then have "restrict(f,\<Union>M) {is continuous}"
      using pasting_lemma1 by auto
    with \<open>M \<in> Pow(?T)\<close> show "\<Union>M \<in> ?T"
      using tau1_is_top IsATopology_def by auto
  qed
  moreover have "\<forall>U\<in>?T.\<forall>V\<in>?T. U\<inter>V \<in> ?T"
    using cont_inter_cont tau1_is_top IsATopology_def by auto
  ultimately show ?thesis using IsATopology_def by simp
qed

text\<open>0 is continuous.\<close>

corollary (in two_top_spaces0) zero_continuous: shows "0 {is continuous}"
proof -
  let ?T = "{U \<in> \<tau>\<^sub>1. restrict(f,U) {is continuous}}"
  have "?T {is a topology}" by (rule pasting_theorem)
  then have "0\<in>?T" by (rule empty_open)
  hence "restrict(f,0) {is continuous}" by simp
  moreover have "restrict(f,0) = 0" by simp
  ultimately show ?thesis by simp
qed

end
