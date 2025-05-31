
section\<open>Two versions of Tarski's Axiom\<close>

theory Tarski_ZF imports ZF.Cardinal

begin

text\<open>A small theory on the Tarski's axiom, inspired by a question on mathoverflow.org.\<close>

subsection\<open>Two versions of the Tarski's axiom\<close>

text\<open>There are two versions of the Tarski's axiom, one adapted from Tarski 1939
  according to Wikipedia's page on Tarski-Grothendieck set theory:

$\forall x.\  \exists y.\  x\in y \wedge  (\forall z\in y.\  \mathcal{P}(z)\in \mathcal{P}(y) 
\wedge  \mathcal{P}(z)\in y) 
\wedge  (\forall z\in \mathcal{P}(y).\  z\approx y \vee  z\in y))$, 

and another one from Metamath, adapted from that page:

$\forall x.\  \exists y.\  x\in y \wedge  (\forall z\in y.\  \mathcal{P}(z)\in \mathcal{P}(y) 
\wedge  (\exists w\in y.\  \mathcal{P}(z)\in \mathcal{P}(w))) 
\wedge  (\forall z.\  z\in \mathcal{P}(y) \longrightarrow  z\approx y \vee  z\in y)$. 

In this section we show that these two versions are equivalent. \<close>

text\<open>The two versions of Tarski's axiom are equivalent.\<close>

theorem Tarski_axioms: shows 
  "(\<forall>x. \<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y) \<and> (\<forall>z\<in>Pow(y). z\<approx>y \<or> z\<in>y))
  \<longleftrightarrow>
  (\<forall>x. \<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> (\<exists>w\<in>y. Pow(z)\<in>Pow(w))) \<and> (\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y))"
proof
  assume T1: "\<forall>x. \<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y) \<and> (\<forall>z\<in>Pow(y). z\<approx>y \<or> z\<in>y)"
  { fix x
    from T1 have "\<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y) \<and> (\<forall>z\<in>Pow(y). z\<approx>y \<or> z\<in>y)"
      by simp
    then obtain y where "x\<in>y" "\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y" "\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y" 
      by auto
    hence 
      "\<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> (\<exists>w\<in>y. Pow(z)\<in>Pow(w))) \<and> (\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y)"
      by auto
  } 
  thus 
    "\<forall>x. \<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> (\<exists>w\<in>y. Pow(z)\<in>Pow(w))) \<and> (\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y)"
    by simp
next
  assume T2: 
    "\<forall>x. \<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> (\<exists>w\<in>y. Pow(z)\<in>Pow(w))) \<and> (\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y)"
  { fix x
    from T2 have 
      "\<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> (\<exists>w\<in>y. Pow(z)\<in>Pow(w))) \<and> (\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y)"
      by simp
    then obtain y where "x\<in>y" and I: "\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> (\<exists>w\<in>y. Pow(z)\<in>Pow(w))" and
      II: "\<forall>z. z\<in>Pow(y) \<longrightarrow> z\<approx>y \<or> z\<in>y" by auto
    from II have III: "\<forall>z\<in>Pow(y). z\<approx>y \<or> z\<in>y" by blast
    { fix z assume "z\<in>y"
      with I have "Pow(z)\<in>Pow(y)" and "\<exists>w\<in>y. Pow(z)\<in>Pow(w)" by simp_all
      then obtain w where "w\<in>y" and "Pow(z)\<in>Pow(w)" by auto
      with I have "Pow(z) \<in> y" by auto
      with I \<open>z\<in>y\<close> have "Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y" by simp
    } hence "\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y" by simp
    with \<open>x\<in>y\<close> III have "\<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y) \<and> (\<forall>z\<in>Pow(y). z\<approx>y \<or> z\<in>y)"
      by auto
  }
  thus "\<forall>x. \<exists>y. x\<in>y \<and> (\<forall>z\<in>y. Pow(z)\<in>Pow(y) \<and> Pow(z)\<in>y) \<and> (\<forall>z\<in>Pow(y). z\<approx>y \<or> z\<in>y)"
    by simp
qed
       
end