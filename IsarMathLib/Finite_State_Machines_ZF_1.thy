(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2023 Daniel de la Concepcion

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

section \<open>Concatenation of languages\<close>

theory Finite_State_Machines_ZF_1 imports Finite_State_Machines_ZF

begin

subsection\<open>Concatenation of regular languages\<close>

text\<open>We now prove the main theorem: the concatenation of two regular
languages is regular.  The proof constructs an \<open>\<epsilon>\<close>-NFSA that first
simulates the automaton for \<open>L\<^sub>1\<close>, then makes a free \<open>\<epsilon>\<close>-transition
to the initial state of the automaton for \<open>L\<^sub>2\<close> upon reaching an
accepting state of the first, and finally accepts when the second
automaton accepts.\<close>

text\<open>The combined state space for the product \<open>\<epsilon>\<close>-NFSA is the
disjoint union \<open>S\<^sub>1\<times>{0}\<union>S\<^sub>2\<times>{1}\<close>.\<close>

definition concat_eNFSA_states where
  "concat_eNFSA_states(S1,S2) \<equiv> S1\<times>{0} \<union> S2\<times>{1}"

text\<open>The transition function of the product \<open>\<epsilon>\<close>-NFSA.
A state \<open>\<langle>s,0\<rangle>\<close> in the first component reads \<open>a\<in>\<Sigma>\<close> by following
\<open>t\<^sub>1\<close>; on the \<open>\<epsilon>\<close>-symbol (encoded as \<open>\<Sigma>\<close>) it jumps to
\<open>\<langle>s\<^sub>02,1\<rangle>\<close> when \<open>s\<in>F\<^sub>1\<close>, and has no \<open>\<epsilon>\<close>-move otherwise.
A state \<open>\<langle>s,1\<rangle>\<close> in the second component reads \<open>a\<in>\<Sigma>\<close> by following
\<open>t\<^sub>2\<close>, and ignores \<open>\<epsilon>\<close>-steps.\<close>

definition concat_eNFSA_trans where
  "Finite(\<Sigma>) \<Longrightarrow>
   (S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
   (S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
   concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>) \<equiv>
     {\<langle>\<langle>\<langle>s,0\<rangle>,q\<rangle>, {t1`\<langle>s,q\<rangle>}\<times>{0}\<rangle>. \<langle>s,q\<rangle>\<in>S1\<times>\<Sigma>}
     \<union> {\<langle>\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>, {x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}\<rangle>. s\<in>S1}
     \<union> {\<langle>\<langle>\<langle>s,1\<rangle>,q\<rangle>, {t2`\<langle>s,q\<rangle>}\<times>{1}\<rangle>. \<langle>s,q\<rangle>\<in>S2\<times>\<Sigma>}
     \<union> {\<langle>\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>, 0\<rangle>. s\<in>S2}"

text\<open>The product automaton is a valid \<open>\<epsilon>\<close>-NFSA.\<close>

lemma concat_eNFSA_valid:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  shows "(concat_eNFSA_states(S1,S2), \<langle>s01,0\<rangle>,
  concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>), F2\<times>{1}
  ){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
proof-
  have S1fin:"Finite(S1)" and S2fin:"Finite(S2)"
    and s01S:"s01\<in>S1" and s02S:"s02\<in>S2"
    and F1S:"F1\<subseteq>S1" and F2S:"F2\<subseteq>S2"
    and t1:"t1:S1\<times>\<Sigma> \<rightarrow> S1" and t2:"t2:S2\<times>\<Sigma> \<rightarrow> S2"
    using A1 A2 unfolding DFSA_def[OF fin] by auto
  let ?SS = "concat_eNFSA_states(S1,S2)"
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  have finS10:"Finite(S1\<times>{0})"
    using Finite1_L12[of S1 "{0}"] Fin_into_Finite Finite_into_Fin S1fin by auto
  have finS21:"Finite(S2\<times>{1})"
    using Finite1_L12[of S2 "{1}"] Fin_into_Finite Finite_into_Fin S2fin by auto
  have finSS:"Finite(?SS)" unfolding concat_eNFSA_states_def
    using finS10 finS21 Finite_Un by auto
  have s01SS:"\<langle>s01,0\<rangle>\<in>?SS" unfolding concat_eNFSA_states_def using s01S by auto
  have F2SS:"F2\<times>{1} \<subseteq> ?SS" unfolding concat_eNFSA_states_def using F2S by auto
  have tc_type:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
  proof-
    have ran:"?tc \<in> Pow((?SS\<times>succ(\<Sigma>))\<times>Pow(?SS))"
    proof-
      {
        fix t assume t:"t\<in>?tc"
        then obtain x y where tt:"\<langle>x,y\<rangle> = t" unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
        with t have xy:"\<langle>x,y\<rangle>\<in>?tc" by auto
        have xy_dom:"x\<in>?SS\<times>succ(\<Sigma>)"
          using xy unfolding concat_eNFSA_trans_def[OF fin A1 A2]
                             concat_eNFSA_states_def
          by (auto intro: succI1 succI2)
        have xy_img:"y\<subseteq>?SS"
        proof-
          from xy consider
            (a) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> y={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> y={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> y=0"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show "y\<subseteq>?SS"
          proof cases
            case a
            then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma>" "y={t1`\<langle>s,aa\<rangle>}\<times>{0}" by auto
            from sa(1) have "t1`\<langle>s,aa\<rangle>\<in>S1" using apply_type[OF t1] by auto
            with sa(2) show ?thesis unfolding concat_eNFSA_states_def by auto
          next
            case b
            then obtain s where sb:"s\<in>S1" "y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" by auto
            then show ?thesis using s02S F2S unfolding concat_eNFSA_states_def by auto
          next
            case c
            then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma>" "y={t2`\<langle>s,aa\<rangle>}\<times>{1}" by auto
            from sa(1) have "t2`\<langle>s,aa\<rangle>\<in>S2" using apply_type[OF t2] by auto
            with sa(2) show ?thesis unfolding concat_eNFSA_states_def by auto
          next
            case d then show ?thesis by auto
          qed
        qed
        from xy_dom xy_img have "\<langle>x,y\<rangle>\<in>(?SS\<times>succ(\<Sigma>))\<times>Pow(?SS)" by auto
        with tt have "t\<in>(?SS\<times>succ(\<Sigma>))\<times>Pow(?SS)" by auto
      }
      then show ?thesis by auto
    qed
    moreover have "function(?tc)"
    proof -
      {
        fix x y z
        assume h1:"\<langle>x,y\<rangle>\<in>?tc" and h2:"\<langle>x,z\<rangle>\<in>?tc"
        from h1 consider
          (a1) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> y={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
          (b1) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
          (c1) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> y={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
          (d1) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> y=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
        then have "y=z"
        proof cases
          case a1
          then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>s,0\<rangle>,aa\<rangle>" "y={t1`\<langle>s,aa\<rangle>}\<times>{0}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(2) sa(2) have "p=s" "q=aa" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
          qed
        next
          case b1
          then obtain s where sa:"s\<in>S1" "x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>" "y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(1,2) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sa(1,2) have "p=s" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
          qed
        next
          case c1
          then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>s,1\<rangle>,aa\<rangle>" "y={t2`\<langle>s,aa\<rangle>}\<times>{1}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(1,2) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(2) sa(1,2) have "p=s" "q=aa" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
          qed
        next
          case d1
          then obtain s where sb:"s\<in>S2" "x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>" "y=0" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(1,2) sb(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sb(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(1,2) sb(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sb(1,2) have "p=s" by auto
            with sb(3) pq(3) show ?thesis by auto
            next
          qed
        qed
      }
      then show ?thesis unfolding function_def by auto
    qed
    moreover have "?SS\<times>succ(\<Sigma>) \<subseteq> domain(?tc)"
    proof
      fix x assume hx:"x\<in>?SS\<times>succ(\<Sigma>)"
      then obtain p aa where pa:"p\<in>?SS" "aa\<in>succ(\<Sigma>)" "x=\<langle>p,aa\<rangle>" by auto
      from pa(1) obtain s where ps:
        "(s\<in>S1 \<and> p=\<langle>s,0\<rangle>) \<or> (s\<in>S2 \<and> p=\<langle>s,1\<rangle>)"
        unfolding concat_eNFSA_states_def by auto
      from pa(2) have acase:"aa\<in>\<Sigma> \<or> aa=\<Sigma>" using succ_iff by auto
      from ps show "x\<in>domain(?tc)"
      proof (elim disjE conjE)
        assume hs1:"s\<in>S1" and hsp1:"p=\<langle>s,0\<rangle>"
        from acase show ?thesis
        proof (elim disjE)
          assume "aa\<in>\<Sigma>"
          with hs1 hsp1 pa(3) have "\<langle>x,{t1`\<langle>s,aa\<rangle>}\<times>{0}\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        next
          assume "aa=\<Sigma>"
          with hs1 hsp1 pa(3) have "\<langle>x,{v\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        qed
      next
        assume hs2:"s\<in>S2" and hsp2:"p=\<langle>s,1\<rangle>"
        from acase show ?thesis
        proof (elim disjE)
          assume "aa\<in>\<Sigma>"
          with hs2 hsp2 pa(3) have "\<langle>x,{t2`\<langle>s,aa\<rangle>}\<times>{1}\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        next
          assume "aa=\<Sigma>"
          with hs2 hsp2 pa(3) have "\<langle>x,0\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        qed
      qed
    qed
    ultimately show ?thesis unfolding Pi_def by auto
  qed
  show ?thesis unfolding FullNFSA_def[OF fin]
    using finSS s01SS F2SS tc_type by auto
qed

text\<open>The $\varepsilon$-transition of a component-0 state $\langle s,0\rangle$
is $\{\langle s_{02},1\rangle\}$ when $s\in F_1$, and empty otherwise.\<close>

lemma concat_eNFSA_eps_comp0:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS1:"s\<in>S1"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>
         = {x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS1 unfolding concat_eNFSA_states_def by (auto intro: succI1)
  have "\<langle>\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>, {x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS1 by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>"] pair by auto
qed

text\<open>The $\varepsilon$-transition of a component-1 state $\langle s,1\rangle$ is empty.\<close>

lemma concat_eNFSA_eps_comp1:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS2:"s\<in>S2"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> = 0"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS2 unfolding concat_eNFSA_states_def by (auto intro: succI1)
  have "\<langle>\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>, 0\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS2 by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>"] pair by auto
qed

text\<open>The normal transition of a component-0 state $\langle s,0\rangle$
is a transition of the first DFSA.\<close>

lemma concat_eNFSA_eps_comp0':
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS1:"s\<in>S1" and sig:"q\<in>\<Sigma>"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,0\<rangle>,q\<rangle>
         = {t1`\<langle>s,q\<rangle>}\<times>{0}"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,0\<rangle>,q\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS1 sig unfolding concat_eNFSA_states_def by auto
  have "\<langle>\<langle>\<langle>s,0\<rangle>,q\<rangle>, {t1`\<langle>s,q\<rangle>}\<times>{0}\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS1 sig by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,0\<rangle>,q\<rangle>"] pair by auto
qed

text\<open>The normal transition of a component-1 state $\langle s,1\rangle$ is
a normal transition of the second DFSA.\<close>

lemma concat_eNFSA_eps_comp1':
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS2:"s\<in>S2" and sig:"q\<in>\<Sigma>"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,1\<rangle>,q\<rangle> = {t2`\<langle>s,q\<rangle>}\<times>{1}"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,1\<rangle>,q\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS2 sig unfolding concat_eNFSA_states_def by (auto)
  have "\<langle>\<langle>\<langle>s,1\<rangle>,q\<rangle>, {t2`\<langle>s,q\<rangle>}\<times>{1}\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS2 sig by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,1\<rangle>,q\<rangle>"] pair by auto
qed

text\<open>The normal transition of a component-1 state $\langle s,1\rangle$ is
a normal transition of the second DFSA.\<close>

lemma concat_eNFSA_eps_closure:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sig:"q\<in>Pow(S)"
  shows "\<epsilon>-cl(S,t,\<Sigma>,q) = q \<union> {x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1) \<noteq>0}"
proof
  from sig have sub:"q \<subseteq> concat_eNFSA_states(S1,S2)" unfolding S_def by auto
  {
    fix y assume "y\<in>\<epsilon>-cl(S,t,\<Sigma>,q)"
    then obtain P where P:"P\<in>Pow(S)" "y\<in>P" "\<langle>q,P\<rangle>\<in>({\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}^*)"
      unfolding S_def t_def EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2] sub] by auto
    let ?r = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
    {
      assume "\<langle>q,P\<rangle>\<in>id(field(?r))"
      then have "P=q" by auto
      with P(2) have "y:q" by auto
      then have "y: q \<union> {x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1) \<noteq>0}" by auto
    } moreover
    {
      assume "\<langle>q,P\<rangle>\<notin>id(field(?r))"
      moreover from P(3) have "\<langle>q,P\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)" using rtrancl_unfold by auto
      ultimately have "\<langle>q,P\<rangle>\<in>(?r O ?r^*)" by auto
      then obtain Q where q:"\<langle>q,Q\<rangle>\<in>?r^*" "\<langle>Q,P\<rangle>\<in>?r" using compE by auto
      from q(2) have p:"P={s\<in>S. \<exists>u\<in>Q. s\<in>t`\<langle>u,\<Sigma>\<rangle>}" "Q\<in>Pow(S)" by auto
      from P(2) p(1) obtain u where u:"u\<in>Q" "y\<in>t`\<langle>u,\<Sigma>\<rangle>" by auto
      {
        assume "u\<in>S1\<times>1"
        then obtain us where uu:"u=\<langle>us,0\<rangle>" "us\<in>S1" by auto
        then have t:"t`\<langle>u,\<Sigma>\<rangle> = {x\<in>{\<langle>s02,1\<rangle>}. us\<in>F1}" using concat_eNFSA_eps_comp0[OF fin A1 A2]
          unfolding t_def by auto
        {
          assume "us\<notin>F1"
          with t have False using u(2) by auto
        }
        then have "us\<in>F1" by auto
        with t have "t`\<langle>u,\<Sigma>\<rangle> = {\<langle>s02,1\<rangle>}" by auto
        with u(2) have "y=\<langle>s02,1\<rangle>" by auto moreover
        from uu(1) `us\<in>F1` have "u\<in>F1\<times>1" by auto
        ultimately have "u\<in>F1\<times>1" "y=\<langle>s02,1\<rangle>" by auto
      } moreover
      {
        assume as:"u\<notin>S1\<times>1"
        from u(1) p(2) have "u:(S1\<times>1)\<union>(S2\<times>{1})" unfolding concat_eNFSA_states_def S_def by auto
        with as have "u\<in>S2\<times>{1}" by auto
        then obtain sq where "sq\<in>S2" "u=\<langle>sq,1\<rangle>" by auto
        then have t:"t`\<langle>u,\<Sigma>\<rangle> = 0" using concat_eNFSA_eps_comp1[OF fin A1 A2] t_def by auto
        with u(2) have False by auto
      }
      ultimately
      have A:"u\<in>F1\<times>{0}" "y=\<langle>s02,1\<rangle>" by auto
      {
        assume "\<langle>q,Q\<rangle>\<in>id(field(?r))"
        then have "q=Q" by auto
        with A(1) u(1) have "q\<inter>(F1\<times>1)\<noteq>0" by auto
        with A(2) have "y\<in>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by auto
        then have "y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by auto
      } moreover
      {
        assume "\<langle>q,Q\<rangle>\<notin>id(field(?r))"
        moreover from q(1) have "\<langle>q,Q\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)" using rtrancl_unfold by auto
        ultimately have "\<langle>q,Q\<rangle>\<in>(?r O ?r^*)" by auto
        then obtain w where q:"\<langle>q,w\<rangle>\<in>?r^*" "\<langle>w,Q\<rangle>\<in>?r" using compE by auto
        from q(2) have "Q={s\<in>S. \<exists>g\<in>w. s\<in>t`\<langle>g,\<Sigma>\<rangle>}" "w\<in>Pow(S)" by auto
        with u(1) obtain v where v:"v\<in>w" "u\<in>t`\<langle>v,\<Sigma>\<rangle>" by auto
        {
           assume "v\<in>S1\<times>1"
          then obtain us where uu:"v=\<langle>us,0\<rangle>" "us\<in>S1" by auto
          then have t:"t`\<langle>v,\<Sigma>\<rangle> = {x\<in>{\<langle>s02,1\<rangle>}. us\<in>F1}" using concat_eNFSA_eps_comp0[OF fin A1 A2]
            unfolding t_def by auto
          {
            assume "us\<notin>F1"
            with t have False using v(2) by auto
          }
          then have "us\<in>F1" by auto
          with t have "t`\<langle>v,\<Sigma>\<rangle> = {\<langle>s02,1\<rangle>}" by auto
          with v(2) have "u=\<langle>s02,1\<rangle>" by auto
          with A(1) have False by auto
        }
        then have as:"v\<notin>S1\<times>1" by auto
        from v(1) `w\<in>Pow(S)` have "v:(S1\<times>1)\<union>(S2\<times>{1})" unfolding concat_eNFSA_states_def S_def by auto
        with as have "v\<in>S2\<times>{1}" by auto
        then obtain sq where "sq\<in>S2" "v=\<langle>sq,1\<rangle>" by auto
        then have t:"t`\<langle>v,\<Sigma>\<rangle> = 0" using concat_eNFSA_eps_comp1[OF fin A1 A2] t_def by auto
        with v(2) have False by auto
      } ultimately
      have "y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by blast
    } ultimately
    have "y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by blast
  }
  then show "\<epsilon>-cl(S, t, \<Sigma>, q) \<subseteq>
    q \<union>
    {x \<in> {\<langle>s02, 1\<rangle>}.
     q \<inter> F1 \<times> 1 \<noteq> \<emptyset>}" by blast
next
  from sig have sub:"q \<subseteq> concat_eNFSA_states(S1,S2)" unfolding S_def by auto 
  from A1 have subSt:"F1 \<subseteq> S1" unfolding DFSA_def[OF fin] by auto
  from A2 have init2:"s02\<in>S2" unfolding DFSA_def[OF fin] by auto
  let ?r = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
  {
    fix y assume as:"y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}"
    {
      assume "y\<in>q"
      then have "y\<in>\<epsilon>-cl(S, t, \<Sigma>, q)" using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2] sub]
        S_def t_def by auto
    } moreover
    {
      assume "y\<notin>q"
      with as have as:"y\<in>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by auto
      {
        assume "q\<inter>(F1\<times>1) = 0"
        with as have False by auto
      }
      then have ne:"q\<inter>(F1\<times>1)\<noteq>0" by auto
      with as have y:"y=\<langle>s02,1\<rangle>" by auto
      from ne obtain qq where qq:"qq\<in>F1" "\<langle>qq,0\<rangle>\<in>q" by auto
      from qq(1) have "t`\<langle>\<langle>qq,0\<rangle>,\<Sigma>\<rangle> = {y}" using y concat_eNFSA_eps_comp0[OF fin A1 A2, of qq] subSt t_def by auto
      then have "y:t`\<langle>\<langle>qq,0\<rangle>,\<Sigma>\<rangle>" by auto
      with qq(2) have "\<exists>m\<in>q. y\<in>t`\<langle>m,\<Sigma>\<rangle>" by blast
      moreover have "y:S" using y init2 S_def concat_eNFSA_states_def by auto
      ultimately have B:"y\<in>{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>}" by auto
      have "\<langle>q,{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>}\<rangle>\<in>?r" using sig by auto
      then have "\<langle>q,{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>}\<rangle>\<in>?r^*" using r_into_rtrancl by auto
      then have "{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>} \<subseteq> \<epsilon>-cl(S, t, \<Sigma>, q)"
        using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2] sub]
          S_def t_def by auto
      with B have "y\<in>\<epsilon>-cl(S, t, \<Sigma>, q)" by auto
    }
    ultimately have "y\<in>\<epsilon>-cl(S, t, \<Sigma>, q)" by auto
  }
  then show "q \<union>
    {x \<in> {\<langle>s02, 1\<rangle>}.
     q \<inter> F1 \<times> 1 \<noteq> \<emptyset>} \<subseteq> \<epsilon>-cl(S, t, \<Sigma>, q)" by auto
qed

text\<open>Once L2 is reached, the relation is equivalent to its DFSA\<close>

lemma concat_FSA_apply_L2_step:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"\<langle>\<langle>j,p\<rangle>,\<langle>r,q\<rangle>\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" "j\<noteq>0"
  and states:"\<langle>p,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,P)" "P\<in>Pow(S)"
  shows "\<exists>Q\<in>Pow(S). \<langle>q,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> (\<langle>\<langle>j,P\<rangle>,\<langle>r,Q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*))"
proof-
  let ?r="{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  from j(1) have "\<langle>j,p\<rangle>\<in>field(({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*)" using fieldI1 by auto
  then have "\<langle>j,p\<rangle>\<in>field({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)" using rtrancl_field by auto
  then have jl:"j\<in>Lists(\<Sigma>)" using DetFinStateAuto.reduce_field(1) A2 unfolding DetFinStateAuto_def
    using fin by blast
  have "\<exists>Q\<in>Pow(S). \<langle>snd(\<langle>r, q\<rangle>),1\<rangle> \<in> \<epsilon>-cl(S,t,\<Sigma>,Q) \<and> \<langle>\<langle>j, P\<rangle>, fst(\<langle>r,q\<rangle>), Q\<rangle> \<in> ?r^*"
  proof(rule rtrancl_induct[OF j(1), where P="\<lambda>s. \<exists>Q\<in>Pow(S). \<langle>snd(s),1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> (\<langle>\<langle>j,P\<rangle>,\<langle>fst(s),Q\<rangle>\<rangle>\<in>(?r^*))"])
    have "j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList j(2) jl by auto
    with states(2) have "\<langle>j,P\<rangle>\<in>field(?r)" using eps_nfsa_field(2)[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def by auto
    then have "\<langle>\<langle>j,P\<rangle>,\<langle>j,P\<rangle>\<rangle>\<in>?r^*" using rtrancl_refl by auto
    with states show "\<exists>Q\<in>Pow(S).
      \<langle>snd(\<langle>j, p\<rangle>),1\<rangle> \<in> \<epsilon>-cl(S,t,\<Sigma>,Q) \<and>
      \<langle>\<langle>j, P\<rangle>, fst(\<langle>j, p\<rangle>),
      Q\<rangle> \<in> ?r^*" by auto
  next
    fix y z assume as:"\<langle>\<langle>j,p\<rangle>,y\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" 
    "\<langle>y,z\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)" 
    "\<exists>Q\<in>Pow(S). \<langle>snd(y),1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> \<langle>\<langle>j,P\<rangle>,fst(y),Q\<rangle>\<in>?r^*" 
    from as(2) obtain yl ys where yz:"yl\<in>NELists(\<Sigma>)" "ys\<in>S2" "y=\<langle>yl,ys\<rangle>" "z=\<langle>Init(yl),t2`\<langle>ys,Last(yl)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF fin A2] by auto
    from yz(3) as(3) obtain Qy where Q:"Qy\<in>Pow(S)" "\<langle>ys,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)" "\<langle>\<langle>j,P\<rangle>,yl,Qy\<rangle>\<in>?r^*" by auto
    have "\<langle>\<langle>yl,Qy\<rangle>,Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r"
      unfolding FullNFSAExecutionRelation_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          S_def t_def s\<^sub>0_def using yz(1) Q(1) S_def by auto
    with Q(3) have "\<langle>\<langle>j,P\<rangle>,Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r^*"
      using rtrancl_into_rtrancl by auto
    with yz(4) have A:"\<langle>\<langle>j,P\<rangle>,fst(z),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r^*" by auto
    from yz(1) have "Last(yl)\<in>\<Sigma>" using last_type by auto
    then have C1:"t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle>={t2`\<langle>ys,Last(yl)\<rangle>}\<times>{1}" using concat_eNFSA_eps_comp1'[OF fin A1 A2 yz(2)]
      unfolding t_def by auto
    have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using concat_eNFSA_valid[OF fin A1 A2]
      unfolding t_def FullNFSA_def[OF fin] s\<^sub>0_def S_def by auto
    have unionS:"\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)} \<in> Pow(S)"
    proof
      {
        fix x assume "x \<in> \<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}"
        then obtain ss where ss:"ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)" "x\<in>t`\<langle>ss,Last(yl)\<rangle>" by auto
        from Q(1) ss(1) have ssS:"ss\<in>S" using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          unfolding S_def t_def by auto
        have lastSig:"Last(yl)\<in>succ(\<Sigma>)" using last_type[OF yz(1)] by auto
        have "\<langle>ss,Last(yl)\<rangle>\<in>S\<times>succ(\<Sigma>)" using ssS lastSig by auto
        from apply_type[OF tT this] ss(2) have "x\<in>S" by auto
      }
      then show "\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)} \<subseteq> S" by auto
    qed
    then have B:"\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<in>Pow(S)" 
      using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] S_def t_def by auto
    then have D:"\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})) = \<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})"
      using epsilon_cl_idem[OF fin concat_eNFSA_valid[OF fin A1 A2]] unionS S_def t_def by auto
    have "Qy \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,Qy)" using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      using Q(1) S_def t_def by auto
    with Q(2) have s:"t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle> \<subseteq> \<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}" by auto
    with unionS have C2:"\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle>) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})"
      using epsilon_cl_mono[OF fin concat_eNFSA_valid[OF fin A1 A2]] unfolding S_def t_def by auto
    from unionS s have "t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle> \<subseteq> S" by auto
    then have "t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle> \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle>)" using
      epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      unfolding S_def t_def by auto
    with C1 C2 have "\<langle>t2`\<langle>ys,Last(yl)\<rangle>,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})" by auto
    with D have C:"\<langle>t2`\<langle>ys,Last(yl)\<rangle>,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}))" by auto
    from A B C yz(4) show "\<exists>Q\<in>Pow(S). \<langle>snd(z),1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> \<langle>\<langle>j,P\<rangle>,fst(z),Q\<rangle>\<in>?r^*" by auto
  qed
  then show ?thesis by auto
qed

text\<open>Once the only thing left is a word in L2, it passes if s02 is one of the initial
states.\<close>

lemma concat_FSA_apply_L2:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  defines "L1 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
  defines "L2 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"j\<in>L2" "\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)" "Q\<in>Pow(S)" "j\<noteq>0"
  shows "\<exists>q\<in>Pow(S). ((\<epsilon>-cl(S,t,\<Sigma>,q) \<inter> F \<noteq> \<emptyset>) \<and> (\<langle>\<langle>j,Q\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)))"
proof-
  from j(4) j(1) have jne:"j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList unfolding L2_def by auto
  from j(1) have l2:"j <-D (S2,s02,t2,F2){in alphabet}\<Sigma>" "j\<in>Lists(\<Sigma>)" unfolding L2_def by auto
  from l2(1) j(4) have "\<exists>q\<in>F2. \<langle>\<langle>j, s02\<rangle>, \<emptyset>, q\<rangle> \<in> ({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*"
    unfolding DFSASatisfy_def[OF fin A2 l2(2)] by auto
  then obtain u where u:"u\<in>F2" "\<langle>\<langle>j,s02\<rangle>,0,u\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*"
    by auto
  have "\<exists>Qa\<in>Pow(S).
      \<langle>u, 1\<rangle> \<in> \<epsilon>-cl(S,t,\<Sigma>,Qa) \<and>
      \<langle>\<langle>j, Q\<rangle>, 0, Qa\<rangle> \<in>
      ({reduce \<epsilon>-N-relation} (S,t){in alphabet}\<Sigma>)^*"
    using concat_FSA_apply_L2_step[OF fin A1 A2 u(2) j(4)] 
    j(2,3) unfolding S_def t_def s\<^sub>0_def by auto
  then obtain H where h:"H\<in>Pow(S)" "\<langle>u,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,H)" "\<langle>\<langle>j,Q\<rangle>,0,H\<rangle>\<in>({reduce \<epsilon>-N-relation} (S,t){in alphabet}\<Sigma>)^*"
    by auto
  from u(1) have "\<langle>u,1\<rangle>\<in>F" unfolding F_def by auto
  moreover note h(2)
  ultimately have "\<epsilon>-cl(S,t,\<Sigma>,H)\<inter>F\<noteq>0" by auto
  with h(1,3) show ?thesis by auto
qed

text\<open>Concatenating a list on the left of a non-empty list yields a non-empty list.\<close>

text\<open>Step 2 (sub-goal of concat\_FSA\_apply\_L1\_step): Concat preserves the non-empty list property
when the right argument is non-empty.\<close>

lemma concat_is_list:
  assumes "p\<in>Lists(X)" "b\<in>Lists(X)"
  shows "Concat(p,b)\<in>Lists(X)"
proof-
  from assms(1) obtain n where n:"n\<in>nat" "p:n\<rightarrow>X" unfolding Lists_def by auto
  from assms(2) obtain k where k:"k\<in>nat" "b:k\<rightarrow>X" unfolding Lists_def by auto
  from n k have Cab:"Concat(p,b):n#+k\<rightarrow>X" using concat_props(1)[OF n(1) k(1)] by auto
  from n(1) k(1) have nk:"n#+k\<in>nat" by auto
  with Cab show ?thesis unfolding Lists_def by auto
qed

lemma concat_is_NElist:
  assumes "p\<in>Lists(X)" "b\<in>NELists(X)"
  shows "Concat(p,b)\<in>NELists(X)"
proof-
  from assms(1) obtain n where n:"n\<in>nat" "p:n\<rightarrow>X" unfolding Lists_def by auto
  from assms(2) obtain k where k:"k\<in>nat" "b:succ(k)\<rightarrow>X" unfolding NELists_def by auto
  from n k have Cab:"Concat(p,b):n#+succ(k)\<rightarrow>X" using concat_props(1)[OF n(1) nat_succI[OF k(1)]] by auto
  from n(1) k(1) have eq:"n#+succ(k) = succ(n#+k)" using add_succ_right by auto
  from n(1) k(1) have nk:"n#+k\<in>nat" by auto
  with Cab eq have "Concat(p,b):succ(n#+k)\<rightarrow>X" by auto
  then show ?thesis unfolding NELists_def using nk by auto
qed

lemma concat_0_left:
  assumes "p\<in>Lists(X)"
  shows "Concat(p,0) = p"
proof-
  from assms(1) obtain n where n:"n\<in>nat" "p:n\<rightarrow>X" unfolding Lists_def by auto
  have k:"0\<in>nat" "0:0\<rightarrow>X" unfolding Pi_def function_def by auto
  from n k have Cab:"Concat(p,0):n\<rightarrow>X" "\<forall>i\<in>n. Concat(p,0)`i = p`i" using concat_props(1,2)[OF n(1) k(1)] by auto
  then show ?thesis using n(2) fun_extension[of "Concat(p,0)" n "\<lambda>_. X" p "\<lambda>_. X"] by auto
qed

text\<open>Step 3 (sub-goal of concat\_FSA\_apply\_L1\_step): The last element of a left-extended
non-empty list is the same as the last element of the original non-empty list.\<close>

lemma concat_last_NElist:
  assumes "p\<in>Lists(X)" "b\<in>NELists(X)"
  shows "Last(Concat(p,b)) = Last(b)"
proof-
  from assms(1) obtain n where n:"n\<in>nat" "p:n\<rightarrow>X" unfolding Lists_def by auto
  from assms(2) obtain k where k:"k\<in>nat" "b:succ(k)\<rightarrow>X" unfolding NELists_def by auto
  from n k have Cab:"Concat(p,b):n#+succ(k)\<rightarrow>X" using concat_props(1)[OF n(1) nat_succI[OF k(1)]] by auto
  from n(1) k(1) have eq:"n#+succ(k) = succ(n#+k)" using add_succ_right by auto
  from n(1) k(1) have nk:"n#+k\<in>nat" by auto
  with Cab eq have Cab':"Concat(p,b):succ(n#+k)\<rightarrow>X" by auto
  have "Last(Concat(p,b)) = Concat(p,b)`(n#+k)" using last_seq_elem[OF Cab'] by auto
  also have "\<dots> = b`(k)" using concat_props(4)[OF n(1) nat_succI[OF k(1)] n(2) k(2)] by auto
  also have "\<dots> = Last(b)" using last_seq_elem[OF k(2)] by auto
  finally show ?thesis .
qed

text\<open>Step 4 (sub-goal of concat\_FSA\_apply\_L1\_step): Init distributes over Concat from the right:
init of the concatenation is the concatenation with the init of the right part.\<close>

lemma concat_init_NElist:
  assumes "p\<in>Lists(X)" "b\<in>NELists(X)"
  shows "Init(Concat(p,b)) = Concat(p,Init(b))"
proof-
  from assms(1) obtain n where n:"n\<in>nat" "p:n\<rightarrow>X" unfolding Lists_def by auto
  from assms(2) obtain k where k:"k\<in>nat" "b:succ(k)\<rightarrow>X" unfolding NELists_def by auto
  have ib:"Init(b):k\<rightarrow>X" using init_props(1)[OF k(1) k(2)] by auto
  have Cib:"Concat(p,Init(b)):n#+k\<rightarrow>X" using concat_props(1)[OF n(1) k(1) n(2) ib] by auto
  from k(2) have bk:"b`(k)\<in>X" using apply_funtype by auto
  from n(1) k(1) have nk:"n#+k\<in>nat" by auto
  have key:"Append(Concat(p,Init(b)),b`(k)) = Concat(p,b)"
    using concat_init_last_elem[OF n(1) k(1) n(2) k(2)] by auto
  have "Init(Append(Concat(p,Init(b)),b`(k))) = Concat(p,Init(b))"
    using init_append[OF nk Cib bk] by auto
  with key show ?thesis by auto
qed

text\<open>Running a word of the form Concat(v,j) to v in a DFSA is
the same as running j from the same starting state.\<close>

lemma (in DetFinStateAuto) dfa_run_suffix:
  assumes vL:"v\<in>Lists(\<Sigma>)" and jNE:"j\<in>NELists(\<Sigma>)"
    and run:"\<langle>\<langle>Concat(v,j),s\<rangle>,\<langle>v,q\<rangle>\<rangle>\<in>r\<^sub>D^*"
  shows "\<langle>\<langle>j,s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*"
proof-
  from jNE obtain n where n:"n\<in>nat" "j:succ(n)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
  let ?P="\<lambda>k. \<forall>v\<in>Lists(\<Sigma>). \<forall>j. j:succ(k)\<rightarrow>\<Sigma> \<longrightarrow>
      (\<forall>s q. \<langle>\<langle>Concat(v,j),s\<rangle>,\<langle>v,q\<rangle>\<rangle>\<in>r\<^sub>D^* \<longrightarrow> \<langle>\<langle>j,s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*)"
  \<comment> \<open>Base case: j is a one-element list\<close>
  have base:"?P(0)"
  proof(intro ballI allI impI)
    fix v' j' s' q'
    assume vL':"v'\<in>Lists(\<Sigma>)" and j1':"j':succ(0)\<rightarrow>\<Sigma>"
      and run1':"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
    from j1' nat_0I have jNE':"j'\<in>NELists(\<Sigma>)" unfolding NELists_def by auto
    from j1' nat_0I have initj':"Init(j'):0\<rightarrow>\<Sigma>" using init_props(1)[of 0 j'] by auto
    then have initj'0:"Init(j')=0" unfolding Pi_def function_def by auto
    have lastj':"Last(j')\<in>\<Sigma>" using last_type[OF jNE'] by auto
    have Cvj':"Concat(v',j')\<in>NELists(\<Sigma>)" using concat_is_NElist[OF vL' jNE'] by auto
    \<comment> \<open>Extract first step: id case is impossible because domains differ\<close>
    have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> id(field(r\<^sub>D)) \<union> (r\<^sub>D^* O r\<^sub>D)"
      using rtrancl_rev[of r\<^sub>D] run1' by auto
    then have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D"
    proof
      assume id:"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>id(field(r\<^sub>D))"
      then have ceq:"Concat(v',j')=v'" by auto
      from vL' obtain m where m:"m\<in>nat" "v':m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
      have "Concat(v',j'):m#+succ(0)\<rightarrow>\<Sigma>" using concat_props(1)[OF m(1) nat_succI[OF nat_0I] m(2) j1'] by auto
      with ceq m(2) have "m#+succ(0) = m" using domain_of_fun[of v' m "\<lambda>_. \<Sigma>"] domain_of_fun[of "Concat(v',j')" "m #+ 1" "\<lambda>_. \<Sigma>"] by auto
      with m(1) have "succ(m) = m" using add_succ_right by auto moreover
      have "m\<in>succ(m)" by auto
      ultimately have "m\<in>m" using subst[of "succ(m)" m "\<lambda>q. m\<in>q"] by blast
      then show ?thesis using mem_irrefl[of m] by auto
    next
      assume "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D" 
      then show "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D" .
    qed
    then have "\<And>P. (\<And>y. \<langle>\<langle>Concat(v',j'),s'\<rangle>,y\<rangle>\<in>r\<^sub>D \<Longrightarrow> \<langle>y,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^* \<Longrightarrow> P) \<Longrightarrow> P"
      using compE[of "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>" "r\<^sub>D" "r\<^sub>D^*"] by auto
    then obtain y where step:"\<langle>\<langle>Concat(v',j'),s'\<rangle>,y\<rangle>\<in>r\<^sub>D" "\<langle>y,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*" .
    from step(1) have yww:
      "y=\<langle>Init(Concat(v',j')),t`\<langle>s',Last(Concat(v',j'))\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    have lastEq:"Last(Concat(v',j'))=Last(j')" using concat_last_NElist[OF vL' jNE'] by auto
    have initEq:"Init(Concat(v',j'))=Concat(v',Init(j'))"
      using concat_init_NElist[OF vL' jNE'] by auto
    from yww lastEq initEq initj'0 have yeq:
      "y=\<langle>Concat(v',0),t`\<langle>s',Last(j')\<rangle>\<rangle>" by auto
    have "Concat(v',0)=v'" using concat_0_left[OF vL'] by auto
    with yeq have yeq2:"y=\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>" by auto
    \<comment> \<open>Remaining run from v' forces q'=t(s',Last(j'))\<close>
    from step(2) yeq2 have remrun:"\<langle>\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    from remrun have "\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>\<in>field(r\<^sub>D)"
      using rtrancl_field relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
    then have rfld:"\<langle>\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using rtrancl_refl by auto
    from remrun rfld have q'eq:"q'=t`\<langle>s',Last(j')\<rangle>" using relation_deteministic by blast
    \<comment> \<open>One step on j' gives the conclusion\<close>
    have jstep:"\<langle>\<langle>j',s'\<rangle>,\<langle>Init(j'),t`\<langle>s',Last(j')\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D"
  using step(1) unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
      using jNE' by auto
    from jstep initj'0 q'eq show "\<langle>\<langle>j',s'\<rangle>,\<langle>0,q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using r_into_rtrancl by auto
  qed
  \<comment> \<open>Inductive step: Init(j) has type succ(k), apply IH\<close>
  have step:"\<And>k. k\<in>nat \<Longrightarrow> ?P(k) \<Longrightarrow> ?P(succ(k))"
  proof-
    fix k assume kn:"k\<in>nat" and IH:"?P(k)"
    show "?P(succ(k))"
    proof(intro ballI allI impI)
    fix v' j' s' q'
    assume vL':"v'\<in>Lists(\<Sigma>)" and jk':"j':succ(succ(k))\<rightarrow>\<Sigma>"
      and run':"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
    from jk' nat_succI[OF kn] have jNE':"j'\<in>NELists(\<Sigma>)" unfolding NELists_def by auto
    from jk' kn have initj':"Init(j'):succ(k)\<rightarrow>\<Sigma>" using init_props(1)[OF nat_succI[OF kn]] by auto
    then have initjNE':"Init(j')\<in>NELists(\<Sigma>)" unfolding NELists_def using kn by auto
    have lastj':"Last(j')\<in>\<Sigma>" using last_type[OF jNE'] by auto
    have Cvj':"Concat(v',j')\<in>NELists(\<Sigma>)" using concat_is_NElist[OF vL' jNE'] by auto
    \<comment> \<open>Extract first step\<close>
    have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> id(field(r\<^sub>D)) \<union> (r\<^sub>D^* O r\<^sub>D)"
      using rtrancl_rev[of r\<^sub>D] run' by auto
    then have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D"
    proof
      assume id:"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>id(field(r\<^sub>D))"
      then have ceq:"Concat(v',j')=v'" by auto
      from vL' obtain m where m:"m\<in>nat" "v':m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
      have A:"Concat(v',j'):m#+succ(succ(k))\<rightarrow>\<Sigma>" using concat_props(1)[OF m(1) _ m(2) jk'] nat_succI kn by auto
      from ceq have "domain(Concat(v',j')) = domain(v')" by auto
      with A have "m#+succ(succ(k)) = domain(v')" using domain_of_fun[of "Concat(v',j')" "m #+ succ(succ(k))" "\<lambda>_. \<Sigma>"]
        by auto
      with m(2) have "m#+succ(succ(k)) = m" using domain_of_fun[of v' m "\<lambda>_. \<Sigma>"] by blast
      with m(1) have "succ(m) = m" using add_succ_right by auto moreover
      have "m\<in>succ(m)" by auto
      ultimately have "m\<in>m" using subst[of "succ(m)" m "\<lambda>q. m\<in>q"] by blast
      then show ?thesis using mem_irrefl[of m] by auto
    next
      assume "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D" 
      then show ?thesis by assumption
    qed
    then obtain y where step':"\<langle>\<langle>Concat(v',j'),s'\<rangle>,y\<rangle>\<in>r\<^sub>D" "\<langle>y,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using compE by auto
    from step'(1) obtain ww ss where yww:
      "ww\<in>NELists(\<Sigma>)" "ss\<in>S" "y=\<langle>Init(ww),t`\<langle>ss,Last(ww)\<rangle>\<rangle>"
      "\<langle>Concat(v',j'),s'\<rangle>=\<langle>ww,ss\<rangle>"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    from yww(4) have wweq:"ww=Concat(v',j')" "ss=s'" by auto
    have lastEq:"Last(Concat(v',j'))=Last(j')" using concat_last_NElist[OF vL' jNE'] by auto
    have initEq:"Init(Concat(v',j'))=Concat(v',Init(j'))"
      using concat_init_NElist[OF vL' jNE'] by auto
    from yww(3) wweq lastEq initEq have yeq:
      "y=\<langle>Concat(v',Init(j')),t`\<langle>s',Last(j')\<rangle>\<rangle>" by auto
    from step'(2) yeq have remrun:
      "\<langle>\<langle>Concat(v',Init(j')),t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    \<comment> \<open>Apply IH to Init(j') to get run from Init(j')\<close>
    from IH initj' vL' have
      "\<forall>s'' q''. \<langle>\<langle>Concat(v',Init(j')),s''\<rangle>,\<langle>v',q''\<rangle>\<rangle>\<in>r\<^sub>D^* \<longrightarrow>
          \<langle>\<langle>Init(j'),s''\<rangle>,\<langle>0,q''\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    with remrun have IHresult:
      "\<langle>\<langle>Init(j'),t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>0,q'\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    \<comment> \<open>One step on j' then chain\<close>
    have jstep:"\<langle>\<langle>j',s'\<rangle>,\<langle>Init(j'),t`\<langle>s',Last(j')\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
      using jNE' yww(2) wweq(2) by auto
    from jstep IHresult show "\<langle>\<langle>j',s'\<rangle>,\<langle>0,q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using rtrancl_into_trancl2 trancl_into_rtrancl by auto
    qed
  qed
  from step have "?P(n)" using nat_induct[of _ ?P, OF n(1) base] by auto
  with vL n(2) run show ?thesis by auto
qed

text\<open>If a DFSA run reduces word w to word v, then v is an initial prefix of w,
i.e., there exists a suffix j with w = Concat(v,j).\<close>

lemma (in DetFinStateAuto) list_prefix_split:
  assumes run: "\<langle>\<langle>w,s\<rangle>,\<langle>v,q\<rangle>\<rangle> \<in> r\<^sub>D^*"
  shows "\<exists> j\<in>Lists(\<Sigma>). w = Concat(v,j)"
proof-
  have wL: "w\<in>Lists(\<Sigma>)"
  proof-
    from run have "\<langle>w,s\<rangle>\<in>field(r\<^sub>D^*)" using fieldI1 by auto
    then have "\<langle>w,s\<rangle>\<in>field(r\<^sub>D)"
      using rtrancl_field[of r\<^sub>D] relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
    then show ?thesis using reduce_field(1) by auto
  qed
  have "\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(\<langle>v,q\<rangle>),j)"
  proof(rule rtrancl_induct[OF run, where P="\<lambda>z. \<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(z),j)"])
    have z:"0\<in>Lists(\<Sigma>)" unfolding Lists_def Pi_def function_def using nat_0I by auto
    with wL have "Concat(fst(\<langle>w,s\<rangle>),0) = w" using concat_0_left by auto
    with z show "\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(\<langle>w,s\<rangle>),j)" using exI[of "\<lambda>j. j\<in>Lists(\<Sigma>) \<and> w= Concat(fst(\<langle>w,s\<rangle>),j)" 0]
      by auto
  next
    fix y z
    assume "\<langle>\<langle>w,s\<rangle>,y\<rangle>\<in>r\<^sub>D^*" "\<langle>y,z\<rangle>\<in>r\<^sub>D" "\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(y),j)"
    from \<open>\<langle>y,z\<rangle>\<in>r\<^sub>D\<close> obtain y1 y2 where y:
      "y1\<in>NELists(\<Sigma>)" "y2\<in>S" "y=\<langle>y1,y2\<rangle>" "z=\<langle>Init(y1),t`\<langle>y2,Last(y1)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    from \<open>\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(y),j)\<close> y(3) obtain j where j:
      "j\<in>Lists(\<Sigma>)" "w = Concat(y1,j)" by auto
    from j(1) obtain m where m:"m\<in>nat" "j:m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
    from y(1) obtain n where n:"n\<in>nat" "y1:succ(n)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
    have lastY:"Last(y1)\<in>\<Sigma>" using last_type[OF y(1)] by auto
    have initY:"Init(y1):n\<rightarrow>\<Sigma>" using init_props(1)[OF n(1) n(2)] by auto
    have sing:"{\<langle>0,Last(y1)\<rangle>}:1\<rightarrow>\<Sigma>" using list_len1_singleton[OF lastY] by auto
    have y1eq:"y1 = Concat(Init(y1),{\<langle>0,Last(y1)\<rangle>})"
    proof-
      have "y1 = Append(Init(y1), Last(y1))"
        using init_props(3)[OF n(1) n(2)] last_seq_elem[OF n(2)] by auto
      also have "Append(Init(y1), Last(y1)) = Concat(Init(y1), {\<langle>0,Last(y1)\<rangle>})"
        using append_concat_pair[OF n(1) initY lastY] by auto
      finally show ?thesis .
    qed
    have assoc:"Concat(Concat(Init(y1),{\<langle>0,Last(y1)\<rangle>}),j) =
        Concat(Init(y1),Concat({\<langle>0,Last(y1)\<rangle>},j))"
      using concat_assoc[OF n(1) _ m(1) initY sing m(2)] by auto
    have jL:"Concat({\<langle>0,Last(y1)\<rangle>},j)\<in>Lists(\<Sigma>)"
    proof-
      have "{\<langle>0,Last(y1)\<rangle>}\<in>Lists(\<Sigma>)"
        using list_len1_singleton[OF lastY] one_is_nat unfolding Lists_def by auto
      then show ?thesis using concat_is_list[OF _ j(1)] by auto
    qed
    from j(2) y1eq assoc have "w = Concat(Init(y1), Concat({\<langle>0,Last(y1)\<rangle>},j))" by auto
    with jL y(4) show "\<exists>j'\<in>Lists(\<Sigma>). w = Concat(fst(z),j')" by auto
  qed
  then show ?thesis by auto
qed

text\<open>Once L1 is reached, the relation is equivalent to its DFSA\<close>

text\<open>Step 1: We prove concat\_FSA\_apply\_L1\_step using the three sub-lemmas above.
Note: the statement requires an additional hypothesis that the prefix s is a list over \<open>\<Sigma>\<close>.\<close>

lemma concat_FSA_apply_L1_step:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"\<langle>\<langle>j,p\<rangle>,\<langle>r,q\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*" "j\<noteq>0"
  and states:"\<langle>p,0\<rangle>\<in>P" "P\<in>Pow(S)"
  and sL:"s\<in>Lists(\<Sigma>)"
  shows "\<exists>Q\<in>Pow(S). \<langle>q,0\<rangle>\<in>Q \<and> (\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,r),Q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*))"
proof-
  let ?r="{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  from j(1) have "\<langle>j,p\<rangle>\<in>field(({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*)" using fieldI1 by auto
  then have "\<langle>j,p\<rangle>\<in>field({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)" using rtrancl_field by auto
  then have jl:"j\<in>Lists(\<Sigma>)" using DetFinStateAuto.reduce_field(1) A1 unfolding DetFinStateAuto_def
    using fin by blast
  have jne:"j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList j(2) jl by auto
  have Csj:"Concat(s,j)\<in>NELists(\<Sigma>)" using concat_is_NElist[OF sL jne] by auto
  have "\<exists>Q\<in>Pow(S). \<langle>snd(\<langle>r,q\<rangle>),0\<rangle>\<in>Q \<and> \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(\<langle>r,q\<rangle>)),Q\<rangle>\<rangle>\<in>?r^*"
  proof(rule rtrancl_induct[OF j(1), where P="\<lambda>v. \<exists>Q\<in>Pow(S). \<langle>snd(v),0\<rangle>\<in>Q \<and> (\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(v)),Q\<rangle>\<rangle>\<in>(?r^*))"])
    from states(2) have "\<langle>Concat(s,j),P\<rangle>\<in>field(?r)"
      using eps_nfsa_field(2)[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def Csj by auto
    then have "\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,j),P\<rangle>\<rangle>\<in>?r^*" using rtrancl_refl by auto
    with states show "\<exists>Q\<in>Pow(S).
      \<langle>snd(\<langle>j,p\<rangle>),0\<rangle>\<in>Q \<and>
      \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(\<langle>j,p\<rangle>)),Q\<rangle>\<rangle>\<in>?r^*" by auto
  next
    fix y z assume as:"\<langle>\<langle>j,p\<rangle>,y\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*"
      "\<langle>y,z\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)"
      "\<exists>Q\<in>Pow(S). \<langle>snd(y),0\<rangle>\<in>Q \<and> \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(y)),Q\<rangle>\<rangle>\<in>?r^*"
    from as(2) obtain yl ys where yz:"yl\<in>NELists(\<Sigma>)" "ys\<in>S1" "y=\<langle>yl,ys\<rangle>" "z=\<langle>Init(yl),t1`\<langle>ys,Last(yl)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF fin A1] by auto
    from yz(3) as(3) obtain Qy where Q:"Qy\<in>Pow(S)" "\<langle>ys,0\<rangle>\<in>Qy" "\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,yl),Qy\<rangle>\<rangle>\<in>?r^*"
      by auto
    have Csyl:"Concat(s,yl)\<in>NELists(\<Sigma>)" using concat_is_NElist[OF sL yz(1)] by auto
    have lastEq:"Last(Concat(s,yl)) = Last(yl)" using concat_last_NElist[OF sL yz(1)] by auto
    have initEq:"Init(Concat(s,yl)) = Concat(s,Init(yl))" using concat_init_NElist[OF sL yz(1)] by auto
    have "\<langle>\<langle>Concat(s,yl),Qy\<rangle>,Init(Concat(s,yl)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(Concat(s,yl))\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r"
      unfolding FullNFSAExecutionRelation_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          S_def t_def s\<^sub>0_def using Csyl Q(1) S_def by auto
    with lastEq initEq
    have step:"\<langle>\<langle>Concat(s,yl),Qy\<rangle>,Concat(s,Init(yl)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r"
      by auto
    with Q(3) have "\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,Init(yl)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?r^*"
      using rtrancl_into_rtrancl by auto
    with yz(4) have A:"\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(z)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?r^*"
      by auto
    from yz(1) have "Last(yl)\<in>\<Sigma>" using last_type by auto
    then have C1:"t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>={t1`\<langle>ys,Last(yl)\<rangle>}\<times>{0}"
      using concat_eNFSA_eps_comp0'[OF fin A1 A2 yz(2)] unfolding t_def by auto
    have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using concat_eNFSA_valid[OF fin A1 A2]
      unfolding t_def FullNFSA_def[OF fin] s\<^sub>0_def S_def by auto
    have unionS:"\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}\<in>Pow(S)"
    proof
      { fix x assume "x\<in>\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}"
        then obtain ss where ss:"ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)" "x\<in>t`\<langle>ss,Last(yl)\<rangle>" by auto
        from Q(1) ss(1) have ssS:"ss\<in>S" using S_def t_def
          EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] by auto
        have lastSig:"Last(yl)\<in>succ(\<Sigma>)" using last_type[OF yz(1)] by auto
        have "\<langle>ss,Last(yl)\<rangle>\<in>S\<times>succ(\<Sigma>)" using ssS lastSig by auto
        from apply_type[OF tT this] ss(2) have "x\<in>S" by auto }
      then show "(\<Union>ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy). t`\<langle>ss,Last(yl)\<rangle>) \<subseteq> S" by auto
    qed
    then have B:"\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<in>Pow(S)"
      using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] S_def t_def by auto
    have "Qy \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,Qy)" using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      using Q(1) S_def t_def by auto
    with Q(2) have sub:"t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>\<subseteq>\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}" by auto
    with unionS have C2:"\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>)\<subseteq>\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})"
      using epsilon_cl_mono[OF fin concat_eNFSA_valid[OF fin A1 A2]] unfolding S_def t_def by auto
    from unionS sub have "t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>\<subseteq>S" by auto
    then have "t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>\<subseteq>\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>)"
      using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      unfolding S_def t_def by auto
    with C1 C2 have C:"\<langle>t1`\<langle>ys,Last(yl)\<rangle>,0\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})" by auto
    from A B C yz(4) show "\<exists>Q\<in>Pow(S). \<langle>snd(z),0\<rangle>\<in>Q \<and> \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(z)),Q\<rangle>\<rangle>\<in>?r^*"
      by auto
  qed
  then show ?thesis by auto
qed

text\<open>Once the only thing left is a word in L1, it passes if s01 is one of the initial
states.\<close>

lemma concat_FSA_apply_L1:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  defines "L1 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
  defines "L2 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"j\<in>L1" "\<langle>s01,0\<rangle>\<in>Q" "Q\<in>Pow(S)" "j\<noteq>0"
  and k:"u\<in>Lists(\<Sigma>)"
  shows "\<exists>q\<in>Pow(S). \<langle>s02,1\<rangle>\<in>q \<and> (\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>u,q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*))"
proof-
  let ?r="({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)"
  from j(1) have jj:"j\<in>Lists(\<Sigma>)" "j <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
    unfolding L1_def by auto
  from jj(2) j(4) obtain q where q:"q\<in>F1" "\<langle>\<langle>j,s01\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*"
    unfolding DFSASatisfy_def[OF fin A1 jj(1)] by auto
  then obtain K where k_def:"K\<in>Pow(S)" "\<langle>q,0\<rangle>\<in>K" "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)"
    using concat_FSA_apply_L1_step[OF fin A1 A2 q(2) j(4,2), of u] j(3) k unfolding S_def t_def s\<^sub>0_def L2_def by auto
  have u:"Concat(u,0) = u" using k concat_0_left[of u] by auto
  {
    assume "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>id(field(?r))"
    then have "Concat(u,j) = u" using u by auto moreover
    from k obtain n where u:"n\<in>nat" "u:n\<rightarrow>\<Sigma>" unfolding L2_def Lists_def by auto
    ultimately have "domain(Concat(u,j)) = n" using func1_1_L1 by auto
    moreover from jj(1) j(4) have "j:NELists(\<Sigma>)" using non_zero_List_func_is_NEList
      by auto
    then obtain k where jk:"k\<in>nat" "j:succ(k)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
    from jk(2) u(2) have "Concat(u,j):n#+succ(k)\<rightarrow>\<Sigma>" using concat_props(1)[OF u(1) nat_succI[OF jk(1)]] by auto
    then have "domain(Concat(u,j)) = n#+succ(k)" using func1_1_L1 by auto
    ultimately have "n=n#+succ(k)" by blast
    then have "n#+0=n#+succ(k)" using add_0_right[OF u(1)] trans[of "n#+0" n "n#+succ(k)"] 
      by blast
    then have "0=succ(k)" using add_left_cancel[OF _ _ _ nat_succI[OF jk(1)], of n n 0] by auto
    then have False by auto
  } moreover
  {
    assume "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<notin>id(field(?r))"
    moreover have "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)"
      using k_def(3) rtrancl_unfold by auto
    ultimately have "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>(?r O ?r^*)" by auto
    then obtain P where P:"\<langle>\<langle>Concat(u,j),Q\<rangle>,P\<rangle>\<in>?r^*" "\<langle>P,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>?r" using compE by auto
    from P(2) have A:"K=\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(fst(P))\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,snd(P))})" "fst(P)\<in>NELists(\<Sigma>)"
      "snd(P)\<in>Pow(S)" using FullNFSAExecutionRelation_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def by auto
    {
      fix w \<sigma> assume as:"w\<in>Pow(S)" "\<sigma>\<in>\<Sigma>"
      have type:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using concat_eNFSA_valid[OF fin A1 A2]
          using FullNFSA_def[OF fin] S_def t_def by auto
      have s:"\<sigma>\<in>succ(\<Sigma>)" using as(2) by auto
      {
        fix m assume "m\<in>\<epsilon>-cl(S,t,\<Sigma>,w)"
        then have "m\<in>S" using as(1) EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          S_def t_def by auto
        with s have "t`\<langle>m,\<sigma>\<rangle>\<in>Pow(S)" using apply_type[OF type] by auto
      }
      then have "\<Union>{t`\<langle>m,\<sigma>\<rangle>. m\<in>\<epsilon>-cl(S,t,\<Sigma>,w)} \<in>Pow(S)" by auto
    }
    moreover from A(2) have "Last(fst(P)):\<Sigma>" using last_type by auto
    moreover note A(3) ultimately
    have "\<Union>{t`\<langle>s,Last(fst(P))\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,snd(P))}\<in>Pow(S)" by auto
    with A(1) have A:"\<epsilon>-cl(S,t,\<Sigma>,K) = K" using epsilon_cl_idem[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def k_def(1) by auto
    have "\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,K)" using concat_eNFSA_eps_closure[OF fin A1 A2]
      k_def(1,2) q(1) unfolding S_def t_def by auto
    with A have "\<langle>s02,1\<rangle>\<in>K" by auto
  }
  ultimately have "\<langle>s02,1\<rangle>\<in>K" by auto
  with k_def(1,3) u show ?thesis by auto
qed

text\<open>The $\varepsilon$-closure of a set of side-1 states stays within side 1:
for $T \subseteq S_2$ we have $\varepsilon$-cl$(S,t,\Sigma,T\times\{1\}) = T\times\{1\}$.
This holds because the $\varepsilon$-transition from every side-1 state is empty
(by \<open>concat_eNFSA_eps_comp1\<close>), so the closure adds nothing.\<close>

lemma epsilon_cl_side1:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sig:"T\<subseteq>S2"
  shows "\<epsilon>-cl(S,t,\<Sigma>,T\<times>{1}) = T\<times>{1}"
proof-
  have TS:"T\<times>{1}\<in>Pow(concat_eNFSA_states(S1,S2))"
    using sig unfolding concat_eNFSA_states_def by auto
  have eq:"\<epsilon>-cl(S,t,\<Sigma>,T\<times>{1}) = T\<times>{1} \<union> {x\<in>{\<langle>s02,1\<rangle>}. (T\<times>{1})\<inter>(F1\<times>1)\<noteq>0}"
    using concat_eNFSA_eps_closure[OF fin A1 A2 TS] unfolding S_def t_def by auto
  have "(T\<times>{1})\<inter>(F1\<times>1) = 0" by auto
  with eq show ?thesis by auto
qed

text\<open>One letter step in the concat $\varepsilon$-NFSA, starting from a state set
of the form $\{\langle q_1,0\rangle\} \cup Q_2\times\{1\}$, produces a state set of the
same form, with the side-0 singleton updated by the DFA transition of $A_1$.\<close>

lemma exec_step_form:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> q1 Q2 ltr
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and q1S1:"q1\<in>S1" and Q2S2:"Q2\<subseteq>S2" and ltrS:"ltr\<in>\<Sigma>"
  shows "\<exists>Q2n\<in>Pow(S2). \<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})})
                  = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union> Q2n\<times>{1}"
proof-
  have t1T:"t1:S1\<times>\<Sigma>\<rightarrow>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have t2T:"t2:S2\<times>\<Sigma>\<rightarrow>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have s02S2:"s02\<in>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have q1'S1:"t1`\<langle>q1,ltr\<rangle>\<in>S1" using apply_type[OF t1T] q1S1 ltrS by auto
  have RS:"{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<in>Pow(concat_eNFSA_states(S1,S2))"
    using q1S1 Q2S2 unfolding concat_eNFSA_states_def by auto
  \<comment> \<open>epsilon-closure of the starting set\<close>
  have ecl:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
    {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  proof-
    have eq:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
      ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) \<union> {x\<in>{\<langle>s02,1\<rangle>}. ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1)\<noteq>0}"
      using concat_eNFSA_eps_closure[OF fin A1 A2 RS] unfolding S_def t_def by auto
    have "({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1) = {x\<in>{\<langle>q1,0\<rangle>}. q1\<in>F1}"
      by auto
    with eq show ?thesis by auto
  qed
  \<comment> \<open>union of t-images over the epsilon-closure\<close>
  let ?cl = "{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  let ?U = "\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>?cl}"
  have step0:"t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle> = {t1`\<langle>q1,ltr\<rangle>}\<times>{0}"
    using concat_eNFSA_eps_comp0'[OF fin A1 A2 q1S1 ltrS] unfolding t_def by auto
  have stepR:"\<And>r. r\<in>Q2 \<Longrightarrow> t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle> = {t2`\<langle>r,ltr\<rangle>}\<times>{1}"
    using Q2S2 ltrS concat_eNFSA_eps_comp1'[OF fin A1 A2 _ ltrS] unfolding t_def by auto
  have stepS02:"t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle> = {t2`\<langle>s02,ltr\<rangle>}\<times>{1}"
    using concat_eNFSA_eps_comp1'[OF fin A1 A2 s02S2 ltrS] unfolding t_def by auto
  have Uform:"?U = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
    ({t2`\<langle>r,ltr\<rangle>. r\<in>Q2} \<union> {x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
  proof(rule equalityI)
    { 
      fix x assume "x\<in>?U"
      then obtain ss where ss:"ss\<in>?cl" "x\<in>t`\<langle>ss,ltr\<rangle>" by auto
      from ss(1) have "ss=\<langle>q1,0\<rangle> \<or> (\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>) \<or> (q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>)" by blast
      moreover { assume "ss=\<langle>q1,0\<rangle>"
        with ss(2) step0 have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>" by auto
        then have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}" by auto }
      moreover { assume "\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "ss=\<langle>r,1\<rangle>" by auto
        with ss(2) stepR[OF r(1)] have "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        with r(1) have "x\<in>{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<times>{1}" by auto }
      moreover { assume "q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>"
        with ss(2) stepS02 have "x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}\<times>{1}"
          using \<open>q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>\<close> by auto }
      ultimately have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
        by auto 
    }
    then show "?U \<subseteq> {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}" by blast
    { fix x assume
        "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
      then have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle> \<or>
        (\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>) \<or> (q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>)" by blast
      moreover { assume "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>"
        then have "x\<in>t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle>" using step0 by auto
        then have "x\<in>?U" by auto }
      moreover { assume "\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle>" using stepR[OF r(1)] by auto
        with r(1) have "x\<in>?U" by auto }
      moreover { assume "q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>"
        then have "x\<in>t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle>" using stepS02 by auto
        then have "x\<in>?U" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
      ultimately have "x\<in>?U" by blast }
    then show "{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1} \<subseteq> ?U"
      by blast
  qed
  (* Q2_mid \<subseteq> S2*)
  let ?Q2mid = "{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}"
  have Q2midS2:"?Q2mid \<subseteq> S2"
  proof
    fix x assume "x\<in>?Q2mid"
    then have "(\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>) \<or> (q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>)" by blast
    moreover { assume "\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>"
      then obtain r where r:"r\<in>Q2" "x=t2`\<langle>r,ltr\<rangle>" by auto
      from Q2S2 r(1) have "r\<in>S2" by auto
      with ltrS have "t2`\<langle>r,ltr\<rangle>\<in>S2" using apply_type[OF t2T] by auto
      with r(2) have "x\<in>S2" by auto }
    moreover { assume "q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>"
      with ltrS have "t2`\<langle>s02,ltr\<rangle>\<in>S2" using apply_type[OF t2T] s02S2 by auto
      then have "x\<in>S2" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
    ultimately show "x\<in>S2" by auto
  qed
  (* U \<in> Pow(S): needed for the second epsilon-closure*)
  have US:"?U\<in>Pow(concat_eNFSA_states(S1,S2))"
    using q1'S1 Q2midS2
    unfolding Uform concat_eNFSA_states_def by auto
  (* second epsilon-closure*)
  have ecl2:"\<epsilon>-cl(S,t,\<Sigma>,?U) = ?U \<union> {x\<in>{\<langle>s02,1\<rangle>}. ?U\<inter>(F1\<times>1)\<noteq>0}"
    using concat_eNFSA_eps_closure[OF fin A1 A2 US] unfolding S_def t_def by auto
  have Uint:"?U\<inter>(F1\<times>1) = {x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}. t1`\<langle>q1,ltr\<rangle>\<in>F1}"
    unfolding Uform by auto
  have "\<epsilon>-cl(S,t,\<Sigma>,?U) = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
    (?Q2mid \<union> {x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1})\<times>{1}"
    using ecl2 Uint Uform by auto
  moreover have "?Q2mid \<union> {x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1} \<subseteq> S2"
    using Q2midS2 s02S2 by auto
  ultimately show ?thesis
    using ecl
    by (intro bexI[of _ "?Q2mid\<union>{x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1}" "Pow(S2)"]) auto
qed

text\<open>Explicit form of the next state set after one step of the concat \<open>\<epsilon>\<close>-NFSA.\<close>

lemma exec_step_Q2_form:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> q1 Q2 ltr
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and q1S1:"q1\<in>S1" and Q2S2:"Q2\<subseteq>S2" and ltrS:"ltr\<in>\<Sigma>"
  shows "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})})
       = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
         ({t2`\<langle>r,ltr\<rangle>. r\<in>Q2} \<union> {x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1} \<union>
          {x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1})\<times>{1}"
proof-
  have t1T:"t1:S1\<times>\<Sigma>\<rightarrow>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have t2T:"t2:S2\<times>\<Sigma>\<rightarrow>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have s02S2:"s02\<in>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have q1'S1:"t1`\<langle>q1,ltr\<rangle>\<in>S1" using apply_type[OF t1T] q1S1 ltrS by auto
  have RS:"{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<in>Pow(concat_eNFSA_states(S1,S2))"
    using q1S1 Q2S2 unfolding concat_eNFSA_states_def by auto
  have ecl:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
    {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  proof-
    have eq:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
      ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) \<union> {x\<in>{\<langle>s02,1\<rangle>}. ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1)\<noteq>0}"
      using concat_eNFSA_eps_closure[OF fin A1 A2 RS] unfolding S_def t_def by auto
    have "({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1) = {x\<in>{\<langle>q1,0\<rangle>}. q1\<in>F1}"
      by auto
    with eq show ?thesis by auto
  qed
  let ?cl = "{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  let ?U = "\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>?cl}"
  have step0:"t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle> = {t1`\<langle>q1,ltr\<rangle>}\<times>{0}"
    using concat_eNFSA_eps_comp0'[OF fin A1 A2 q1S1 ltrS] unfolding t_def by auto
  have stepR:"\<And>r. r\<in>Q2 \<Longrightarrow> t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle> = {t2`\<langle>r,ltr\<rangle>}\<times>{1}"
    using Q2S2 ltrS concat_eNFSA_eps_comp1'[OF fin A1 A2 _ ltrS] unfolding t_def by auto
  have stepS02:"t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle> = {t2`\<langle>s02,ltr\<rangle>}\<times>{1}"
    using concat_eNFSA_eps_comp1'[OF fin A1 A2 s02S2 ltrS] unfolding t_def by auto
  have Uform:"?U = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
    ({t2`\<langle>r,ltr\<rangle>. r\<in>Q2} \<union> {x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
  proof(rule equalityI)
    { fix x assume "x\<in>?U"
      then obtain ss where ss:"ss\<in>?cl" "x\<in>t`\<langle>ss,ltr\<rangle>" by auto
      from ss(1) have "ss=\<langle>q1,0\<rangle> \<or> (\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>) \<or> (q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>)" by blast
      moreover { assume "ss=\<langle>q1,0\<rangle>"
        with ss(2) step0 have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>" by auto
        then have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}" by auto }
      moreover { assume "\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "ss=\<langle>r,1\<rangle>" by auto
        with ss(2) stepR[OF r(1)] have "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        with r(1) have "x\<in>{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<times>{1}" by auto }
      moreover { assume "q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>"
        with ss(2) stepS02 have "x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}\<times>{1}"
          using \<open>q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>\<close> by auto }
      ultimately have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
        by auto }
    then show "?U \<subseteq> {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}" by blast
    { fix x assume
        "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
      then have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle> \<or>
        (\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>) \<or> (q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>)" by blast
      moreover { assume "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>"
        then have "x\<in>t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle>" using step0 by auto
        then have "x\<in>?U" by auto }
      moreover { assume "\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle>" using stepR[OF r(1)] by auto
        with r(1) have "x\<in>?U" by auto }
      moreover { assume "q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>"
        then have "x\<in>t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle>" using stepS02 by auto
        then have "x\<in>?U" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
      ultimately have "x\<in>?U" by blast }
    then show "{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1} \<subseteq> ?U"
      by blast
  qed
  let ?Q2mid = "{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}"
  have US:"?U\<in>Pow(concat_eNFSA_states(S1,S2))"
  proof-
    have Q2midS2:"?Q2mid \<subseteq> S2"
    proof
      fix x assume "x\<in>?Q2mid"
      then have "(\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>) \<or> (q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>)" by blast
      moreover { assume "\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>"
        then obtain r where r:"r\<in>Q2" "x=t2`\<langle>r,ltr\<rangle>" by auto
        from Q2S2 r(1) have "r\<in>S2" by auto
        with ltrS have "t2`\<langle>r,ltr\<rangle>\<in>S2" using apply_type[OF t2T] by auto
        with r(2) have "x\<in>S2" by auto }
      moreover { assume "q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>"
        with ltrS have "t2`\<langle>s02,ltr\<rangle>\<in>S2" using apply_type[OF t2T] s02S2 by auto
        then have "x\<in>S2" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
      ultimately show "x\<in>S2" by auto
    qed
    show ?thesis using q1'S1 Q2midS2 unfolding Uform concat_eNFSA_states_def by auto
  qed
  have ecl2:"\<epsilon>-cl(S,t,\<Sigma>,?U) = ?U \<union> {x\<in>{\<langle>s02,1\<rangle>}. ?U\<inter>(F1\<times>1)\<noteq>0}"
    using concat_eNFSA_eps_closure[OF fin A1 A2 US] unfolding S_def t_def by auto
  have Uint:"?U\<inter>(F1\<times>1) = {x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}. t1`\<langle>q1,ltr\<rangle>\<in>F1}"
    unfolding Uform by auto
  show ?thesis using ecl ecl2 Uint Uform by auto
qed

text\<open>If the concat $\varepsilon$-NFSA executes word $w$ (non-empty) from $\{\langle s_{01},0\rangle\}$
and reaches $\langle v,Q\rangle$, then $Q$ has the form $\{\langle q_1,0\rangle\}\cup Q_2\times\{1\}$
with $q_1\in S_1$, $Q_2\subseteq S_2$, and $A_1$ tracks the word: $\langle\langle w,s_{01}\rangle,\langle v,q_1\rangle\rangle\in r_{D_1}^*$.\<close>

lemma exec_state_form:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> w v Q
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and wNE:"w\<in>NELists(\<Sigma>)"
  and run:"\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,Q\<rangle>\<rangle> \<in> (({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)"
  shows "\<exists>q1\<in>S1. \<exists>Q2\<in>Pow(S2). Q = {\<langle>q1,0\<rangle>} \<union> Q2\<times>{1} \<and>
         \<langle>\<langle>w,s01\<rangle>,\<langle>v,q1\<rangle>\<rangle>\<in>(({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*)"
proof-
  let ?r  = "{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  let ?rD = "{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
  have fsa:"(S,\<langle>s01,0\<rangle>,t,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] unfolding S_def t_def by auto
  have s01S1:"s01\<in>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have wfield:"\<langle>w,s01\<rangle>\<in>field(?rD)"
    using wNE s01S1 DetFinStateAuto.reduce_field(2)
    unfolding DetFinStateAuto_def using A1 fin by blast
  let ?P = "\<lambda>uR. \<exists>q1\<in>S1. \<exists>Q2\<in>Pow(S2). snd(uR) = {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1} \<and>
              \<langle>\<langle>w,s01\<rangle>,\<langle>fst(uR),q1\<rangle>\<rangle>\<in>?rD^*"
  have "?P(\<langle>v,Q\<rangle>)"
  proof(rule rtrancl_induct[of "\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>" "\<langle>v,Q\<rangle>" ?r ?P])
    show "\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,Q\<rangle>\<rangle>\<in>?r^*" using run .
    \<comment> \<open>base case: initial state set \<open>{\<langle>s01,0\<rangle>}\<close> has the form with q1=s01, \<open>Q2=\<emptyset>\<close>\<close>
    show "?P(\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>)"
      using rtrancl_refl[OF wfield] s01S1 by auto
  next
    fix y z
    assume IH_run:"\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,y\<rangle>\<in>?r^*"
      and step:"\<langle>y,z\<rangle>\<in>?r"
      and IH:"?P(y)"
    \<comment> \<open>unpack the \<open>\<epsilon>\<close>-NFSA step: first rewrite the hypothesis, then extract\<close>
    from step have step_unf:"\<langle>y,z\<rangle>\<in>{\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(w)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)})\<rangle>\<rangle>. \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"
      unfolding FullNFSAExecutionRelation_def[OF fin fsa] by simp
    from step_unf obtain yl R where yz:
      "yl\<in>NELists(\<Sigma>)" "R\<in>Pow(S)"
      "y=\<langle>yl,R\<rangle>"
      "z=\<langle>Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,R)})\<rangle>"
      by auto
    \<comment> \<open>unpack the inductive hypothesis\<close>
    from IH yz(3) obtain q1 Q2 where IHd:
      "q1\<in>S1" "Q2\<in>Pow(S2)" "R={\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}"
      "\<langle>\<langle>w,s01\<rangle>,\<langle>yl,q1\<rangle>\<rangle>\<in>?rD^*"
      by auto
    have Q2S2:"Q2\<subseteq>S2" using IHd(2) by auto
    have aS:"Last(yl)\<in>\<Sigma>" using last_type[OF yz(1)] .
    \<comment> \<open>apply \<open>exec_step_form\<close> to get the new structured state\<close>
    from exec_step_form[OF fin A1 A2 IHd(1) Q2S2 aS]
    obtain Q2n where Q2n:"Q2n\<in>Pow(S2)"
      "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})})
       = {\<langle>t1`\<langle>q1,Last(yl)\<rangle>,0\<rangle>}\<union>Q2n\<times>{1}"
      unfolding S_def t_def by auto
    have zform:"z=\<langle>Init(yl),{\<langle>t1`\<langle>q1,Last(yl)\<rangle>,0\<rangle>}\<union>Q2n\<times>{1}\<rangle>"
      using yz(4) Q2n(2) IHd(3) by auto
    \<comment> \<open>DFA tracking: one more step of A1\<close>
    have t1S1:"t1`\<langle>q1,Last(yl)\<rangle>\<in>S1"
      using A1 IHd(1) aS unfolding DFSA_def[OF fin] by (auto intro: apply_type)
    have dfaStep:"\<langle>\<langle>yl,q1\<rangle>,\<langle>Init(yl),t1`\<langle>q1,Last(yl)\<rangle>\<rangle>\<rangle>\<in>?rD"
      unfolding DFSAExecutionRelation_def[OF fin A1] using yz(1) IHd(1) by auto
    have newDfa:"\<langle>\<langle>w,s01\<rangle>,\<langle>Init(yl),t1`\<langle>q1,Last(yl)\<rangle>\<rangle>\<rangle>\<in>?rD^*"
      using rtrancl_into_rtrancl[OF IHd(4) dfaStep] .
    \<comment> \<open>conclude: P(z) holds with \<open>q1_next=t1`\<langle>q1,Last(yl)\<rangle>\<close> and Q2n\<close>
    show "?P(z)" using zform t1S1 Q2n(1) newDfa by auto
  qed
  then show ?thesis by auto
qed

text\<open>For each component-2 state \<open>q2\<close> that appears in the state set reached by
the concat \<open>\<epsilon>\<close>-NFSA after reading non-empty word \<open>w\<close>, either (a) there is a
non-empty suffix \<open>yl_k\<close> of \<open>w\<close> such that A1 ran from \<open>s01\<close> to some \<open>f1\<in>F1\<close>
while consuming the complementary prefix, and A2 then ran from \<open>s02\<close> to \<open>q2\<close>
while consuming \<open>yl_k\<close>; or (b) \<open>q2 = s02\<close> and the \<open>\<epsilon>\<close>-jump into A2 happened
only at the very end, so A1 reached some \<open>f1\<in>F1\<close> after consuming all of \<open>w\<close>.\<close>

lemma exec_A2_component:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> w v q1 Q2 q2
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and wNE:"w\<in>NELists(\<Sigma>)"
  and run:"\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,{\<langle>q1,0\<rangle>} \<union> Q2\<times>{1}\<rangle>\<rangle>
             \<in> (({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)"
  and q1S1:"q1\<in>S1"
  and Q2S2:"Q2\<in>Pow(S2)"
  and q2Q2:"q2\<in>Q2"
  shows "(\<exists>yl_k\<in>NELists(\<Sigma>). \<exists>f1\<in>F1.
            \<langle>\<langle>w,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^* \<and>
            \<langle>\<langle>yl_k,s02\<rangle>,\<langle>v,q2\<rangle>\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*)
         \<or>
         (q2 = s02 \<and> (\<exists>f1\<in>F1.
            \<langle>\<langle>w,s01\<rangle>,\<langle>v,f1\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*))"
proof-
  let ?r\<epsilon> = "{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  let ?rD1 = "{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
  let ?rD2 = "{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
  have s01S1:"s01\<in>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have s02S2:"s02\<in>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have t1T:"t1:S1\<times>\<Sigma>\<rightarrow>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have t2T:"t2:S2\<times>\<Sigma>\<rightarrow>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have fsa:"(S,\<langle>s01,0\<rangle>,t,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] unfolding S_def t_def by auto
  have wfieldD1:"\<langle>w,s01\<rangle>\<in>field(?rD1)"
    using wNE s01S1 DetFinStateAuto.reduce_field(2)
    unfolding DetFinStateAuto_def using A1 fin by blast
  \<comment> \<open>Enriched predicate: tracks A1 state and for every A2 state records \<open>case_a/case_b\<close>.\<close>
  let ?case_a = "\<lambda>q2' v'. \<exists>yl_k\<in>NELists(\<Sigma>). \<exists>f1\<in>F1.
      \<langle>\<langle>w,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^* \<and> \<langle>\<langle>yl_k,s02\<rangle>,\<langle>v',q2'\<rangle>\<rangle>\<in>?rD2^*"
  let ?case_b = "\<lambda>q2' v'. q2'=s02 \<and> (\<exists>f1\<in>F1. \<langle>\<langle>w,s01\<rangle>,\<langle>v',f1\<rangle>\<rangle>\<in>?rD1^*)"
  let ?P = "\<lambda>uR. \<exists>q1'\<in>S1. \<exists>Q2'\<in>Pow(S2). snd(uR) = {\<langle>q1',0\<rangle>}\<union>Q2'\<times>{1} \<and>
      \<langle>\<langle>w,s01\<rangle>,\<langle>fst(uR),q1'\<rangle>\<rangle>\<in>?rD1^* \<and>
      (\<forall>q2'\<in>Q2'. ?case_a(q2', fst(uR)) \<or> ?case_b(q2', fst(uR)))"
  have Pmain:"?P(\<langle>v, {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>)"
  proof(rule rtrancl_induct[of "\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>" "\<langle>v,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>" ?r\<epsilon> ?P])
    show "\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>\<rangle>\<in>?r\<epsilon>^*" using run .
    \<comment> \<open>Base: Q2'=\<open>\<emptyset>\<close>, vacuous \<open>\<forall>\<close>.\<close>
    show "?P(\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>)"
      using rtrancl_refl[OF wfieldD1] s01S1 by auto
  next
    fix y z
    assume step:"\<langle>y,z\<rangle>\<in>?r\<epsilon>"
    assume IH:"?P(y)"
    \<comment> \<open>Unpack the \<open>\<epsilon>\<close>-NFSA step.\<close>
    from step have step_unf:
      "\<langle>y,z\<rangle>\<in>{\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(w)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)})\<rangle>\<rangle>.
        \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"
      unfolding FullNFSAExecutionRelation_def[OF fin fsa] by simp
    from step_unf obtain yl R where yz:
      "yl\<in>NELists(\<Sigma>)" "R\<in>Pow(S)" "y=\<langle>yl,R\<rangle>"
      "z=\<langle>Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,R)})\<rangle>"
      by auto
    \<comment> \<open>Unpack the inductive hypothesis.\<close>
    from IH yz(3) obtain q1ih Q2ih where IHd:
      "q1ih\<in>S1" "Q2ih\<in>Pow(S2)" "R={\<langle>q1ih,0\<rangle>}\<union>Q2ih\<times>{1}"
      "\<langle>\<langle>w,s01\<rangle>,\<langle>yl,q1ih\<rangle>\<rangle>\<in>?rD1^*"
      "\<forall>q2'\<in>Q2ih. ?case_a(q2', yl) \<or> ?case_b(q2', yl)"
      by auto
    have Q2ihS2:"Q2ih\<subseteq>S2" using IHd(2) by auto
    have ltrS:"Last(yl)\<in>\<Sigma>" using last_type[OF yz(1)] .
    \<comment> \<open>Name the letter and the new A1 state.\<close>
    let ?ltr = "Last(yl)"
    let ?q1' = "t1`\<langle>q1ih,?ltr\<rangle>"
    \<comment> \<open>Explicit Q2n via \<open>exec_step_Q2_form\<close>.\<close>
    let ?Q2n = "{t2`\<langle>r,?ltr\<rangle>. r\<in>Q2ih} \<union> {x\<in>{t2`\<langle>s02,?ltr\<rangle>}. q1ih\<in>F1} \<union>
               {x\<in>{s02}. ?q1'\<in>F1}"
    have zform:"z=\<langle>Init(yl),{\<langle>?q1',0\<rangle>}\<union>?Q2n\<times>{1}\<rangle>"
      using exec_step_Q2_form[OF fin A1 A2 IHd(1) Q2ihS2 ltrS] yz(4) IHd(3)
      unfolding S_def t_def by auto
    have q1'S1:"?q1'\<in>S1" using apply_type[OF t1T] IHd(1) ltrS by auto
    have Q2nS2:"?Q2n\<in>Pow(S2)"
    proof-
      { fix x assume "x\<in>?Q2n"
        then have "(\<exists>r\<in>Q2ih. x=t2`\<langle>r,?ltr\<rangle>) \<or> (q1ih\<in>F1 \<and> x=t2`\<langle>s02,?ltr\<rangle>) \<or>
            (?q1'\<in>F1 \<and> x=s02)" by blast
        moreover { assume "\<exists>r\<in>Q2ih. x=t2`\<langle>r,?ltr\<rangle>"
          then obtain r where r:"r\<in>Q2ih" "x=t2`\<langle>r,?ltr\<rangle>" by auto
          from Q2ihS2 r(1) have "r\<in>S2" by auto
          with ltrS have "x\<in>S2" using r(2) apply_type[OF t2T] by auto }
        moreover { assume "q1ih\<in>F1 \<and> x=t2`\<langle>s02,?ltr\<rangle>"
          with ltrS s02S2 have "x\<in>S2" using apply_type[OF t2T] by auto }
        moreover { assume "?q1'\<in>F1 \<and> x=s02"
          with s02S2 have "x\<in>S2" by auto }
        ultimately have "x\<in>S2" by auto }
      then show ?thesis by auto
    qed
    \<comment> \<open>Extend the A1 DFA tracking by one step.\<close>
    have dfaStep1:"\<langle>\<langle>yl,q1ih\<rangle>,\<langle>Init(yl),?q1'\<rangle>\<rangle>\<in>?rD1"
      unfolding DFSAExecutionRelation_def[OF fin A1] using yz(1) IHd(1) by auto
    have newDfa1:"\<langle>\<langle>w,s01\<rangle>,\<langle>Init(yl),?q1'\<rangle>\<rangle>\<in>?rD1^*"
      using rtrancl_into_rtrancl[OF IHd(4) dfaStep1] .
    \<comment> \<open>For every \<open>q2'\<in>Q2n\<close> prove \<open>case_a\<close> or \<open>case_b\<close>.\<close>
    have allQ2n:"\<forall>q2'\<in>?Q2n. ?case_a(q2', Init(yl)) \<or> ?case_b(q2', Init(yl))"
    proof
      fix q2' assume q2'Q2n:"q2'\<in>?Q2n"
      from q2'Q2n have cases:"(\<exists>r\<in>Q2ih. q2'=t2`\<langle>r,?ltr\<rangle>) \<or>
          (q1ih\<in>F1 \<and> q2'=t2`\<langle>s02,?ltr\<rangle>) \<or> (?q1'\<in>F1 \<and> q2'=s02)"
        by blast
      moreover
      { \<comment> \<open>Case: \<open>q2'=t2(r,ltr)\<close> for some \<open>r\<in>Q2ih\<close>.\<close>
        assume "\<exists>r\<in>Q2ih. q2'=t2`\<langle>r,?ltr\<rangle>"
        then obtain r where r:"r\<in>Q2ih" "q2'=t2`\<langle>r,?ltr\<rangle>" by auto
        from Q2ihS2 r(1) have rS2:"r\<in>S2" by auto
        from IHd(5) r(1) have IHr:"?case_a(r, yl) \<or> ?case_b(r, yl)" by auto
        moreover
        { assume ca:"?case_a(r, yl)"
          then obtain yk f1 where yk:
            "yk\<in>NELists(\<Sigma>)" "f1\<in>F1"
            "\<langle>\<langle>w,s01\<rangle>,\<langle>yk,f1\<rangle>\<rangle>\<in>?rD1^*"
            "\<langle>\<langle>yk,s02\<rangle>,\<langle>yl,r\<rangle>\<rangle>\<in>?rD2^*" by auto
          have step2:"\<langle>\<langle>yl,r\<rangle>,\<langle>Init(yl),t2`\<langle>r,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2"
            unfolding DFSAExecutionRelation_def[OF fin A2] using yz(1) rS2 by auto
          have nd2:"\<langle>\<langle>yk,s02\<rangle>,\<langle>Init(yl),t2`\<langle>r,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2^*"
            using rtrancl_into_rtrancl[OF yk(4) step2] .
          have "?case_a(q2', Init(yl))"
            using yk(1,2,3) nd2 r(2) by auto }
        moreover
        { assume cb:"?case_b(r, yl)"
          then have rs02:"r=s02" and "\<exists>f1\<in>F1. \<langle>\<langle>w,s01\<rangle>,\<langle>yl,f1\<rangle>\<rangle>\<in>?rD1^*" by auto
          then obtain f1H where f1H:"f1H\<in>F1" "\<langle>\<langle>w,s01\<rangle>,\<langle>yl,f1H\<rangle>\<rangle>\<in>?rD1^*" by auto
          have step2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2"
            unfolding DFSAExecutionRelation_def[OF fin A2] using yz(1) s02S2 by auto
          have nd2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2^*"
            using r_into_rtrancl step2 by auto
          have "?case_a(q2', Init(yl))"
            using yz(1) f1H(1,2) nd2 r(2) rs02 by auto }
        ultimately have "?case_a(q2', Init(yl)) \<or> ?case_b(q2', Init(yl))" by auto }
      moreover
      { \<comment> \<open>Case: \<open>q1ih\<in>F1\<close> so A2 enters via \<open>\<epsilon>\<close>-jump and takes one step.\<close>
        assume "q1ih\<in>F1 \<and> q2'=t2`\<langle>s02,?ltr\<rangle>"
        then have q1ihF1:"q1ih\<in>F1" and q2form:"q2'=t2`\<langle>s02,?ltr\<rangle>" by auto
        have step2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2"
          unfolding DFSAExecutionRelation_def[OF fin A2] using yz(1) s02S2 by auto
        have nd2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2^*"
          using r_into_rtrancl step2 by auto
        have "?case_a(q2', Init(yl))"
          using yz(1) q1ihF1 IHd(4) nd2 q2form by auto }
      moreover
      { \<comment> \<open>Case: \<open>q1'\<in>F1\<close> so A2 enters at \<open>s02\<close> after this step.\<close>
        assume "?q1'\<in>F1 \<and> q2'=s02"
        then have "?case_b(q2', Init(yl))"
          using newDfa1 by auto }
      ultimately show "?case_a(q2', Init(yl)) \<or> ?case_b(q2', Init(yl))" by auto
    qed
    \<comment> \<open>Assemble \<open>?P(z)\<close>: simplify \<open>fst\<close>/\<open>snd\<close> first, then introduce witnesses.\<close>
    show "?P(z)"
    proof-
      from zform have fstZ:"fst(z) = Init(yl)"
        and sndZ:"snd(z) = {\<langle>?q1',0\<rangle>}\<union>?Q2n\<times>{1}" by auto
      have nd1:"\<langle>\<langle>w,s01\<rangle>,\<langle>fst(z),?q1'\<rangle>\<rangle>\<in>?rD1^*" using fstZ newDfa1 by auto
      have allz:"\<forall>q2''\<in>?Q2n. ?case_a(q2'', fst(z)) \<or> ?case_b(q2'', fst(z))"
        using fstZ allQ2n by auto
      have "\<exists>q1''\<in>S1. \<exists>Q2''\<in>Pow(S2). snd(z) = {\<langle>q1'',0\<rangle>}\<union>Q2''\<times>{1} \<and>
            \<langle>\<langle>w,s01\<rangle>,\<langle>fst(z),q1''\<rangle>\<rangle>\<in>?rD1^* \<and>
            (\<forall>q2''\<in>Q2''. ?case_a(q2'', fst(z)) \<or> ?case_b(q2'', fst(z)))"
        using q1'S1 Q2nS2 sndZ nd1 allz
        by (intro bexI[of _ ?q1' S1] bexI[of _ ?Q2n "Pow(S2)"]) auto
      then show ?thesis by auto
    qed
  qed
  \<comment> \<open>Extract conclusion from \<open>Pmain\<close>.\<close>
  from Pmain obtain q1p Q2p where Pd:
    "q1p\<in>S1" "Q2p\<in>Pow(S2)"
    "{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1} = {\<langle>q1p,0\<rangle>}\<union>Q2p\<times>{1}"
    "\<langle>\<langle>w,s01\<rangle>,\<langle>v,q1p\<rangle>\<rangle>\<in>?rD1^*"
    "\<forall>q2'\<in>Q2p. ?case_a(q2', v) \<or> ?case_b(q2', v)"
    by auto
  have q2Q2p:"q2\<in>Q2p"
  proof-
    have "\<langle>q2,1\<rangle>\<in>Q2\<times>{1}" using q2Q2 by auto
    then have "\<langle>q2,1\<rangle>\<in>{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}" by auto
    with Pd(3) have "\<langle>q2,1\<rangle>\<in>{\<langle>q1p,0\<rangle>}\<union>Q2p\<times>{1}" by auto
    then show "q2\<in>Q2p" by auto
  qed
  from Pd(5) q2Q2p show ?thesis by auto
qed

text\<open>The language of the product \<open>\<epsilon>\<close>-NFSA equals the concatenation
of the two component languages.\<close>

lemma concat_eNFSA_language:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and L1_def:"L1 = {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
  and L2_def:"L2 = {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
  shows "{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (concat_eNFSA_states(S1,S2),
             \<langle>s01,0\<rangle>,
             concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>),
             F2\<times>{1}){in alphabet}\<Sigma>}
        = concat(L1,L2)"
proof-
  have lang1:"L1 {is a language with alphabet}\<Sigma>"
    using L1_def unfolding IsALanguage_def[OF fin] by auto
  have lang2:"L2 {is a language with alphabet}\<Sigma>"
    using L2_def unfolding IsALanguage_def[OF fin] by auto
  let ?s\<^sub>0="\<langle>s01,0\<rangle>"
  let ?S="concat_eNFSA_states(S1,S2)"
  let ?t="concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?F="F2\<times>{1}"
  have ss:"?s\<^sub>0\<in>?S" unfolding concat_eNFSA_states_def using A1 unfolding DFSA_def[OF fin] by auto
  then have ss2:"{?s\<^sub>0} \<subseteq> ?S" by auto
  then have ss3:"{?s\<^sub>0}\<in>Pow(?S)" by auto
  {
    fix i assume "i\<in>{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}"
    then have i:"i\<in>Lists(\<Sigma>)" "i <-\<epsilon>-N (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>" by auto
    from i(2) have r:"(\<exists>q\<in>Pow(?S). (\<epsilon>-cl(?S,?t,\<Sigma>,q) \<inter> ?F \<noteq> \<emptyset>) \<and>
      (\<langle>\<langle>i, {?s\<^sub>0}\<rangle>, \<emptyset>, q\<rangle> \<in>
      (({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)))\<or>(i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>)"
      unfolding FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2] i(1)] by auto
    {
      assume i0:"i=0" and ecl:"\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>"
      have "\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) = {?s\<^sub>0}\<union>{x\<in>{\<langle>s02,1\<rangle>}. s01\<in>F1}" using concat_eNFSA_eps_closure[OF fin A1 A2 ss3] by auto
      moreover have "?s\<^sub>0\<notin>?F" by auto
      ultimately have "\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F = {x\<in>{\<langle>s02,1\<rangle>}. s01\<in>F1}\<inter>?F" by auto
      with ecl obtain p where p:"p\<in>?F" "p\<in>{x\<in>{\<langle>s02,1\<rangle>}. s01\<in>F1}" by auto
      {
        assume "s01\<notin>F1"
        with p(2) have False by auto
      }
      then have s01F1:"s01\<in>F1" by auto
      with p(2) have "p=\<langle>s02,1\<rangle>"  by auto
      with p(1) have s02F2:"s02\<in>F2" by auto
      from i(1) i0 have zero_L:"(0:Lists(\<Sigma>))" by auto
      have "0 <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
        unfolding DFSASatisfy_def[OF fin A1 zero_L] using s01F1 by auto
      then have zero_L1:"(0:L1)" unfolding L1_def using zero_L by auto
      have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
        unfolding DFSASatisfy_def[OF fin A2 zero_L] using s02F2 by auto
      then have zero_L2:"(0:L2)" unfolding L2_def using zero_L by auto
      have concat00:"Concat(0,0) = 0"
        unfolding Concat_def ShiftedSeq_def NatInterval_def by auto
      have "(0:concat(L1,L2))"
        unfolding concat_def[OF lang1 lang2]
        using zero_L2 zero_L1 concat00 by auto
      with i0 have "i:concat(L1,L2)" by auto
    } moreover
    {
      assume "\<not>(i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>)"
      with r obtain q where q:"q:Pow(?S)" "\<epsilon>-cl(?S,?t,\<Sigma>,q) \<inter> ?F \<noteq> \<emptyset>" "\<langle>\<langle>i, {?s\<^sub>0}\<rangle>, \<emptyset>, q\<rangle> \<in>
    (({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)" by auto
      from q(1) have ecl_eq:"\<epsilon>-cl(?S,?t,\<Sigma>,q) = q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}"
        using concat_eNFSA_eps_closure[OF fin A1 A2] by auto
      then have "i:concat(L1,L2)"
      proof -
        let ?r\<epsilon> = "{reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>"
        let ?rD1 = "{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
        let ?rD2 = "{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
        have zero_L:"(0::i)\<in>Lists(\<Sigma>)"
          unfolding Lists_def Pi_def function_def using nat_0I by auto
        \<comment> \<open>Step 1: derive \<open>i\<in>NELists(\<Sigma>)\<close>.
            If \<open>i=0\<close> the \<open>r\<epsilon>^*\<close> run is the identity, forcing \<open>q=\{s\<^sub>0\}\<close> and
            \<open>\<epsilon>-cl(\{s\<^sub>0\})\<inter>F\<noteq>\<emptyset>\<close>, which contradicts the surrounding negated assumption.\<close>
        have iNE:"i\<in>NELists(\<Sigma>)"
        proof (rule ccontr)
          assume inoNE:"i\<notin>NELists(\<Sigma>)"
          from i(1) obtain k where k:"k\<in>nat" "i:k\<rightarrow>\<Sigma>" unfolding Lists_def by auto
          have "k=0"
          proof (rule ccontr)
            assume "k\<noteq>0"
            from k(1) this obtain p where p:"p\<in>nat" "k=succ(p)" using Nat_ZF_1_L3 by auto
            with k(2) have "i:succ(p)\<rightarrow>\<Sigma>" by simp
            then have "i\<in>NELists(\<Sigma>)" unfolding NELists_def using p(1) by auto
            with inoNE show False by simp
          qed
          with k(2) have "i:0\<rightarrow>\<Sigma>" by simp
          then have i0:"i=0" unfolding Pi_def function_def by auto
          from q(3) i0 have run0:"\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>?r\<epsilon>^*" by simp
          from rtrancl_rev[of ?r\<epsilon>] run0 have
            "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>id(field(?r\<epsilon>)) \<union>
             (?r\<epsilon>^* O ?r\<epsilon>)" by auto
          moreover {
            assume "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>id(field(?r\<epsilon>))"
            then have "q={?s\<^sub>0}" by auto
            with q(2) have "\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0})\<inter>?F\<noteq>0" by simp
            with \<open>\<not>(i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>)\<close> i0 have False by auto
          }
          moreover {
            assume "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>?r\<epsilon>^* O ?r\<epsilon>"
            then obtain y where "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,y\<rangle>\<in>?r\<epsilon>" using compE by auto
            then have "0\<in>NELists(\<Sigma>)"
              unfolding FullNFSAExecutionRelation_def[OF fin
                concat_eNFSA_valid[OF fin A1 A2]] by auto
            then have False unfolding NELists_def Pi_def by auto
          }
          ultimately show False by auto
        qed
        \<comment> \<open>Step 2: apply \<open>exec_state_form\<close> to decompose \<open>q\<close>.\<close>
        from exec_state_form[OF fin A1 A2 iNE q(3)] obtain q1 Q2 where qform:
          "q1\<in>S1" "Q2\<in>Pow(S2)" "q={\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}"
          "\<langle>\<langle>i,s01\<rangle>,\<langle>0,q1\<rangle>\<rangle>\<in>?rD1^*"
          by auto
        \<comment> \<open>Step 3: \<open>\<epsilon>-cl(q)\<inter>?F\<noteq>\<emptyset>\<close> forces \<open>Q2\<inter>F2\<noteq>\<emptyset>\<close> or \<open>q1\<in>F1\<and>s02\<in>F2\<close>.\<close>
        have caseSplit:"Q2\<inter>F2\<noteq>0 \<or> (q1\<in>F1 \<and> s02\<in>F2)"
        proof (rule ccontr)
          assume "\<not>(Q2\<inter>F2\<noteq>0 \<or> (q1\<in>F1 \<and> s02\<in>F2))"
          then have Q2F2:"Q2\<inter>F2=0" and notcA:"\<not>(q1\<in>F1 \<and> s02\<in>F2)" by auto
          {
            assume as:"q\<inter>(F1\<times>1)\<noteq>0"
            with qform(3) have "\<langle>q1,0\<rangle>\<in>F1\<times>1" by auto
            then have "q1\<in>F1" by auto
            with notcA have A:"s02\<notin>F2" by auto
            from Q2F2 have "(Q2\<times>{1})\<inter>?F =0" by auto
            then have "q\<inter>?F = 0" using qform(3) by auto moreover
            from as ecl_eq have "\<langle>s02,1\<rangle>:\<epsilon>-cl(?S,?t,\<Sigma>,q)" by auto
            ultimately have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = {\<langle>s02,1\<rangle>}\<inter>?F"
              using ecl_eq by auto
            with A have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = 0" by auto
            with q(2) have False by auto
          }
          then have "q\<inter>(F1\<times>1) =0" by auto
          then have "\<epsilon>-cl(?S,?t,\<Sigma>,q) = q" using ecl_eq by auto
          then have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = q\<inter>?F" by auto
          then have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = (Q2\<inter>F2)\<times>{1}" using qform(3) by auto
          with Q2F2 have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = 0" by auto
          with q(2) show False by auto
        qed
        have D1:"DetFinStateAuto(S1,s01,t1,F1,\<Sigma>)"
          unfolding DetFinStateAuto_def using fin A1 by auto
        have D2:"DetFinStateAuto(S2,s02,t2,F2,\<Sigma>)"
          unfolding DetFinStateAuto_def using fin A2 by auto
        have s01S1:"s01\<in>S1" using A1 unfolding DFSA_def[OF fin] by auto
        \<comment> \<open>\<open>Concat(0,i)=i\<close>: used to build the witness \<open>i=Concat(0,i)\<close> in concat.\<close>
        have C0i:"Concat(0,i)=i"
        proof -
          from i(1) obtain k where k:"k\<in>nat" "i:k\<rightarrow>\<Sigma>" unfolding Lists_def by auto
          have zk:"(0::i):0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
          have t1c:"Concat(0,i):k\<rightarrow>\<Sigma>"
            using concat_props(1)[OF nat_0I k(1) zk k(2)] add_0 k(1) by simp
          have ptw:"\<forall>j\<in>k. Concat(0,i)`j = i`j"
          proof
            fix j assume jk:"j\<in>k"
            from jk k(1) have jN:"j\<in>nat" using elem_nat_is_nat by blast
            then have s:"0 #+ j = j" by auto
            have jI:"0 #+ j\<in>NatInterval(0,k)"
              using jk unfolding NatInterval_def by auto
            from concat_props(3)[OF nat_0I k(1) zk k(2)] jI jN
            show "Concat(0,i)`j = i`j" by auto
          qed
          from t1c k(2) ptw show "Concat(0,i)=i"
            using fun_extension[of "Concat(0,i)" k "\<lambda>_. \<Sigma>" i "\<lambda>_. \<Sigma>"] by auto
        qed
        \<comment> \<open>Shared helper: \<open>i\<in>L1\<close> and \<open>0\<in>L2\<close> imply \<open>i\<in>concat(L1,L2)\<close> via \<open>Concat(0,i)=i\<close>.\<close>
        have conc_from_L1_0L2:"i\<in>L1 \<Longrightarrow> 0\<in>L2 \<Longrightarrow> i\<in>concat(L1,L2)"
        proof -
          assume "i\<in>L1" "0\<in>L2"
          then have "\<langle>i,0\<rangle>\<in>L1\<times>L2" by auto
          then have "Concat(0,i):concat(L1,L2)" unfolding concat_def[OF lang1 lang2] by auto
          then show "i\<in>concat(L1,L2)" using C0i by auto
        qed
        have run_A2:"\<langle>\<langle>i,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>0,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>\<rangle>\<in>?r\<epsilon>^*"
          using q(3) qform(3) by auto
        from caseSplit show "i\<in>concat(L1,L2)"
        proof (elim disjE)
          \<comment> \<open>Case B: pick \<open>q2\<in>Q2\<inter>F2\<close> and apply \<open>exec_A2_component\<close>.\<close>
          assume cB:"Q2\<inter>F2\<noteq>0"
          then obtain q2 where q2:"q2\<in>Q2" "q2\<in>F2" by auto
          from exec_A2_component[OF fin A1 A2 iNE run_A2 qform(1) qform(2) q2(1)]
          show "i\<in>concat(L1,L2)"
          proof (elim disjE)
            \<comment> \<open>case\_a: A1 ran \<open>i\<close> to \<open>yl_k\<in>NELists\<close>, then A2 ran \<open>yl_k\<close> to \<open>q2\<in>F2\<close>.\<close>
            assume "\<exists>yl_k\<in>NELists(\<Sigma>). \<exists>f1\<in>F1.
                      \<langle>\<langle>i,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^* \<and>
                      \<langle>\<langle>yl_k,s02\<rangle>,\<langle>0,q2\<rangle>\<rangle>\<in>?rD2^*"
            then obtain yl_k f1 where
              yk_ne:"yl_k\<in>NELists(\<Sigma>)" and f1F1:"f1\<in>F1" and
              ca1:"\<langle>\<langle>i,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^*" and
              ca2:"\<langle>\<langle>yl_k,s02\<rangle>,\<langle>0,q2\<rangle>\<rangle>\<in>?rD2^*" by auto
            have ykL:"yl_k\<in>Lists(\<Sigma>)" using yk_ne unfolding NELists_def Lists_def by auto
            have yk_L2:"yl_k\<in>L2"
            proof -
              have "yl_k <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A2 ykL] using q2(2) ca2 by auto
              then show "yl_k\<in>L2" unfolding L2_def using ykL by auto
            qed
            from DetFinStateAuto.list_prefix_split[OF D1 ca1] obtain jl where
              jl_L:"jl\<in>Lists(\<Sigma>)" and i_spl:"i=Concat(yl_k,jl)" by auto
            \<comment> \<open>\<open>jl\<in>L1\<close>: if \<open>jl=0\<close> use determinism to get \<open>s01\<in>F1\<close>;
                otherwise apply \<open>dfa_run_suffix\<close>.\<close>
            have jlL1:"jl\<in>L1"
            proof -
              {
                assume jl0:"jl=0"
                have ieq:"i=yl_k"
                  using jl0 i_spl concat_0_left[OF ykL] by simp
                with ca1 have same:"\<langle>\<langle>yl_k,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^*" by simp
                have fld:"\<langle>yl_k,s01\<rangle>\<in>field(?rD1)"
                  using DetFinStateAuto.reduce_field(2)[OF D1] yk_ne s01S1 by auto
                have id_r:"\<langle>\<langle>yl_k,s01\<rangle>,\<langle>yl_k,s01\<rangle>\<rangle>\<in>?rD1^*"
                  using rtrancl_refl fld by auto
                from DetFinStateAuto.relation_deteministic[OF D1 same id_r]
                have "f1=s01" .
                with f1F1 have s01F1:"s01\<in>F1" by simp
                have "0 <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
                  unfolding DFSASatisfy_def[OF fin A1 zero_L] using s01F1 by auto
                with jl0 have "jl\<in>L1" unfolding L1_def using zero_L by auto
              } moreover {
                assume "jl\<noteq>0"
                from jl_L obtain m where m:"m\<in>nat" "jl:m\<rightarrow>\<Sigma>"
                  unfolding Lists_def by auto
                  {
                    assume "m=0"
                    with m(2) have "jl=0" by auto
                    with \<open>jl\<noteq>0\<close> have False by auto
                  }
                with m(1) obtain p where p:"p\<in>nat" "m=succ(p)"
                  using Nat_ZF_1_L3 by auto
                with m(2) have jlNE:"jl\<in>NELists(\<Sigma>)"
                  unfolding NELists_def using p(1) by auto
                from i_spl ca1 have
                  rspl:"\<langle>\<langle>Concat(yl_k,jl),s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^*" by simp
                from DetFinStateAuto.dfa_run_suffix[OF D1 ykL jlNE rspl]
                have rjl:"\<langle>\<langle>jl,s01\<rangle>,\<langle>0,f1\<rangle>\<rangle>\<in>?rD1^*" .
                have "jl <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
                  unfolding DFSASatisfy_def[OF fin A1 jl_L] using f1F1 rjl by auto
                then have "jl\<in>L1" unfolding L1_def using jl_L by auto
              }
              ultimately show "jl\<in>L1" by auto
            qed
            show "i\<in>concat(L1,L2)"
              unfolding concat_def[OF lang1 lang2] i_spl using jlL1 yk_L2 by auto
          next
            \<comment> \<open>case\_b: \<open>q2=s02\<close> and A1 ran all of \<open>i\<close> to some \<open>f1\<in>F1\<close>.\<close>
            assume cb:"q2=s02 \<and> (\<exists>f1\<in>F1. \<langle>\<langle>i,s01\<rangle>,\<langle>0,f1\<rangle>\<rangle>\<in>?rD1^*)"
            then have s02F2:"s02\<in>F2" using q2(2) by auto
            from cb obtain f1 where f1F1:"f1\<in>F1" and
              cb1:"\<langle>\<langle>i,s01\<rangle>,\<langle>0,f1\<rangle>\<rangle>\<in>?rD1^*" by auto
            have iL1:"i\<in>L1"
            proof -
              have "i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A1 i(1)] using f1F1 cb1 by auto
              then show "i\<in>L1" unfolding L1_def using i(1) by auto
            qed
            have zL2:"0\<in>L2"
            proof -
              have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A2 zero_L] using s02F2 by auto
              then show "0\<in>L2" unfolding L2_def using zero_L by auto
            qed
            show "i\<in>concat(L1,L2)" using conc_from_L1_0L2 iL1 zL2 by auto
          qed
        next
          \<comment> \<open>Case A: \<open>q1\<in>F1\<close> and \<open>s02\<in>F2\<close>.  A1 accepted \<open>i\<close>; \<open>0\<in>L2\<close> by \<open>s02\<in>F2\<close>.\<close>
          assume cA:"q1\<in>F1 \<and> s02\<in>F2"
          then have q1F1:"q1\<in>F1" and s02F2:"s02\<in>F2" by auto
          have iL1:"i\<in>L1"
          proof -
            have "i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
              unfolding DFSASatisfy_def[OF fin A1 i(1)] using q1F1 qform(4) by auto
            then show "i\<in>L1" unfolding L1_def using i(1) by auto
          qed
          have zL2:"0\<in>L2"
          proof -
            have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
              unfolding DFSASatisfy_def[OF fin A2 zero_L] using s02F2 by auto
            then show "0\<in>L2" unfolding L2_def using zero_L by auto
          qed
          show "i\<in>concat(L1,L2)" using conc_from_L1_0L2 iL1 zL2 by auto
        qed
      qed
    } ultimately
    have "i:concat(L1,L2)" by auto
  } moreover
  {
    fix i assume "i:concat(L1,L2)"
    then obtain j u where uj:"u\<in>L2" "j\<in>L1" "i=Concat(u,j)" using concat_def[OF lang1 lang2] by auto
    from uj have c:"Concat(u,j)\<in>Lists(\<Sigma>)" unfolding L1_def L2_def using concat_is_list by auto
    {
      assume j0:"j\<noteq>0" moreover
      from uj(1) have uu:"u\<in>Lists(\<Sigma>)" unfolding L2_def by auto moreover
      have "{\<langle>s01,0\<rangle>}\<subseteq>S1\<times>1" using A1 unfolding DFSA_def[OF fin] by auto
      then have "{\<langle>s01,0\<rangle>}\<in>Pow(?S)" unfolding concat_eNFSA_states_def by auto
      ultimately obtain Q1 where A:"Q1\<in>Pow(?S)" "\<langle>s02,1\<rangle>\<in>Q1" 
        "\<langle>\<langle>Concat(u,j),{\<langle>s01,0\<rangle>}\<rangle>,u,Q1\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
        using concat_FSA_apply_L1[OF fin A1 A2, of j "{\<langle>s01,0\<rangle>}" u] uj(2) unfolding L1_def
        by auto
      from A have A22:"\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(?S,?t,\<Sigma>,Q1)"
        using concat_eNFSA_eps_closure[OF fin A1 A2] by auto
      {
        assume u0:"u\<noteq>0"
        from concat_FSA_apply_L2[OF fin A1 A2 _ A22 A(1) u0] uj(1)
          obtain Q2 where B:"Q2\<in>Pow(?S)" " \<epsilon>-cl(?S,?t,\<Sigma>,Q2)\<inter>?F\<noteq>0"
          "\<langle>\<langle>u,Q1\<rangle>,0,Q2\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
          unfolding L2_def by auto
        from A(3) B(3) have "\<langle>\<langle>Concat(u,j),{?s\<^sub>0}\<rangle>,0,Q2\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
          using trans_rtrancl[of "({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)"]
          unfolding trans_def by auto
        then have "Concat(u,j) <-\<epsilon>-N (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>"
          using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] B(1,2)
          c by auto
        with uj(3) c have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
      } moreover
      {
        assume u0:"u=0"
        {
          assume "s02\<in>F2"
          with A(2) have "Q1\<inter>?F\<noteq>0" by auto moreover
          from A(1) have "Q1 \<subseteq> \<epsilon>-cl(?S,?t,\<Sigma>,Q1)" using epsilon_cl_refl_sub[OF fin
            concat_eNFSA_valid[OF fin A1 A2]] by auto
          ultimately have "\<epsilon>-cl(?S,?t,\<Sigma>,Q1)\<inter>?F\<noteq>0" by auto
          with A(1,3) have "Concat(u,j) <-\<epsilon>-N (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>"
            using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2], of "Concat(u,j)"]
            c `u=0` by auto
          with uj(3) c have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
        } moreover
        {
          assume G:"s02\<notin>F2"
          let ?dr="{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
          have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
          then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
          from u0 uj(1) have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>" unfolding L2_def by auto
          with l0 obtain q where q:"q\<in>F2" "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" 
            using DFSASatisfy_def[OF fin A2, of 0] G by auto
          {
            assume "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))"
            then have False using G q(1) by auto
          }
          then have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<notin>id(field(?dr))" by auto moreover
          from q(2) have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))\<union>(?dr^* O ?dr)" using rtrancl_rev
            by auto
          ultimately have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>(?dr^* O ?dr)" by auto
          then obtain y where y:"\<langle>\<langle>0,s02\<rangle>,y\<rangle>\<in>?dr" "\<langle>y,\<langle>0,q\<rangle>\<rangle>\<in>?dr^*" using compE by auto
          from y(1) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF fin A2]
            by auto
          then have False unfolding NELists_def Pi_def by auto
        }
        ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
      }
      ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
    } moreover
    {
      assume j0:"j=0"
      then have iu:"i=u" using concat_0_left uj(3) uj(1) unfolding L2_def by auto
      have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
      then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
      {
        assume G:"s01\<notin>F1"
        let ?dr="{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
        from j0 uj(2) have "0 <-D (S1,s01,t1,F1){in alphabet}\<Sigma>" unfolding L1_def by auto
        with l0 obtain q where q:"q\<in>F1" "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*" 
          using DFSASatisfy_def[OF fin A1, of 0] G by auto
        {
          assume "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>id(field(?dr))"
          then have False using G q(1) by auto
        }
        then have "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<notin>id(field(?dr))" by auto moreover
        from q(2) have "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>id(field(?dr))\<union>(?dr^* O ?dr)" using rtrancl_rev
          by auto
        ultimately have "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>(?dr^* O ?dr)" by auto
        then obtain y where y:"\<langle>\<langle>0,s01\<rangle>,y\<rangle>\<in>?dr" "\<langle>y,\<langle>0,q\<rangle>\<rangle>\<in>?dr^*" using compE by auto
        from y(1) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF fin A1]
          by auto
        then have False unfolding NELists_def Pi_def by auto
      }
      then have "s01\<in>F1" by auto moreover
      have p:"{\<langle>s01,0\<rangle>}:Pow(?S)" using A1 unfolding concat_eNFSA_states_def
        DFSA_def[OF fin] by auto
      ultimately have B:"\<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>}) = {\<langle>s01,0\<rangle>,\<langle>s02,1\<rangle>}"
        using concat_eNFSA_eps_closure[OF fin A1 A2, of "{\<langle>s01,0\<rangle>}"] by auto
      {
        assume u0:"u=0"
        {
          assume G:"s02\<notin>F2"
          let ?dr="{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
          from u0 uj(1) have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>" unfolding L2_def by auto
          with l0 obtain q where q:"q\<in>F2" "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" 
            using DFSASatisfy_def[OF fin A2, of 0] G by auto
          {
            assume "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))"
            then have False using G q(1) by auto
          }
          then have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<notin>id(field(?dr))" by auto moreover
          from q(2) have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))\<union>(?dr^* O ?dr)" using rtrancl_rev
            by auto
          ultimately have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>(?dr^* O ?dr)" by auto
          then obtain y where y:"\<langle>\<langle>0,s02\<rangle>,y\<rangle>\<in>?dr" "\<langle>y,\<langle>0,q\<rangle>\<rangle>\<in>?dr^*" using compE by auto
          from y(1) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF fin A2]
            by auto
          then have False unfolding NELists_def Pi_def by auto
        }
        then have "s02\<in>F2" by auto
        then have A:"\<langle>s02,1\<rangle>\<in>?F" by auto
        from A B have "\<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>}) \<inter>?F \<noteq>0" by auto
        with iu u0 have "i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>}) \<inter>?F \<noteq>0" by auto
        then have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" 
            using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
            l0 iu u0 by auto
      } moreover
      {
        assume u0:"u\<noteq>0"
        from B have B:"\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>})" by auto
        from concat_FSA_apply_L2[OF fin A1 A2 _ B p u0] uj(1) B
          obtain Q2 where B:"Q2\<in>Pow(?S)" " \<epsilon>-cl(?S,?t,\<Sigma>,Q2)\<inter>?F\<noteq>0"
          "\<langle>\<langle>u,{\<langle>s01,0\<rangle>}\<rangle>,0,Q2\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
          unfolding L2_def by auto
        then have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" using iu uj(1) unfolding L2_def
            using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
            by auto
      }
      ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
    }
    ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
  }
  ultimately show ?thesis by blast
qed

text\<open>The concatenation of two regular languages is regular.\<close>

theorem concat_language_regular:
  assumes fin:"Finite(\<Sigma>)"
  and "L1{is a regular language on}\<Sigma>"
  and "L2{is a regular language on}\<Sigma>"
  shows "concat(L1,L2) {is a regular language on}\<Sigma>"
proof-
  from fin assms(2) obtain S1 s01 t1 F1 where
    A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
    and "L1 = DetFinStateAuto.LanguageDFSA(S1,s01,t1,F1,\<Sigma>)"
    using IsRegularLanguage_def by auto
  then have A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
    and L1_eq:"L1 = {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def fin A1 by auto
  from fin assms(3) obtain S2 s02 t2 F2 where
    A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
    and "L2 = DetFinStateAuto.LanguageDFSA(S2,s02,t2,F2,\<Sigma>)"
    using IsRegularLanguage_def by auto
  then have A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
    and L2_eq:"L2 = {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def fin A2 by auto
  let ?SS = "concat_eNFSA_states(S1,S2)"
  let ?s0 = "\<langle>s01,0\<rangle>"
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?Fc = "F2\<times>{1}"
  have valid:"(?SS,?s0,?tc,?Fc){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have lang_eq:"{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (?SS,?s0,?tc,?Fc){in alphabet}\<Sigma>} = concat(L1,L2)"
    using concat_eNFSA_language[OF fin A1 A2 L1_eq L2_eq] .
  have "{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (?SS,?s0,?tc,?Fc){in alphabet}\<Sigma>} {is a regular language on}\<Sigma>"
    using epsilonNFSA_lang_is_regular[OF fin valid] .
  with lang_eq show ?thesis by auto
qed

end
