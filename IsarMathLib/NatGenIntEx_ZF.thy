(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2011 Victor Porton

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Generalizations - an example application\<close>

theory NatGenIntEx_ZF imports ZF.Int Generalization_ZF

begin

text\<open>This theory shows an example application of of the setup for 
  generalization presented in \<open>Generalization_ZF.\<close>\<close>

text \<open>In this example I show that integers can be considered 
  as a generalization of natural numbers. The next \<open>interpretion\<close>
  shows that we can use theorems proven in the \<open>generalization\<close>
  locale to sets \<open>nat\<close>, \<open>int\<close> and the natural embedding
  of natural numbers into integers.\<close>

interpretation int_interpr: 
  generalization "nat" "int" "{\<langle>n,int_of(n)\<rangle>. n \<in> nat}"
proof -
  let ?f = "{\<langle>n,int_of(n)\<rangle>. n \<in> nat}"
  have "?f \<in> inj(nat,int)"
  proof -
    have I: "?f: nat \<rightarrow> int" using ZF_fun_from_total by simp
    moreover from I have "\<forall>n\<in>nat. ?f`(n)= int_of(n)" 
      using ZF_fun_from_tot_val by simp
    moreover have "\<forall>n\<in>nat.\<forall>m\<in>nat. int_of(n)=int_of(m) \<longrightarrow> n=m"
      using int_of_inject by simp
    ultimately show ?thesis using inj_def by simp
  qed
  then show "generalization(nat,int,?f)" using generalization_def by simp
qed


text \<open>Next we prove that ZF generalization is an arbitrary generalization.
  This allows to access notions defined in \<open>generalization1\<close> locale 
  from within \<open>generalization\<close> locale.\<close>

sublocale 
  generalization \<subseteq> generalization1 small big embed zf_newbig zf_move
proof
  show "zf_move\<in>bij(big, zf_newbig)" using zf_move_bij by auto
  show "zf_move O embed = id(small)" using zf_embed_move by auto
qed

abbreviation "int_obj \<equiv> int_interpr.zf_newbig"

text \<open>Naturals are a subset of integers.\<close>

lemma "nat \<subseteq> int_obj" using int_interpr.small_less_zf_newbig by auto

text \<open>An example of defining an operation on the generalization set.\<close>

definition add where
  "add(x,y) \<equiv> int_interpr.zf_move`(int_interpr.ret`x $+ int_interpr.ret`y)"

end