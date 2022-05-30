(*
    This file is part of isar2html2.0 - a tool for rendering IsarMathLib
	theories in in HTML.
    Copyright (C) 2022  Slawomir Kolodynski
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

module Tests

open Xunit
open FParsec

open iml.IMLParser
open iml.IMLP_datatypes
open iml.ProcessThys
open iml.Export2Html
open iml.Utils
open iml.IsarSym2Latex

/// converts parser to a debug parser 
/// that returns position before and after
let dbgp (p: Parser<_,_>) stream =
    let posBefore = getPosition stream
    let r = (p |>> fun x -> (x,posBefore,getPosition stream))
    r

let test p str parsed =
    match run p str with
    | Success(result, _, _)   -> Assert.Equal(parsed,result)
    | Failure(errorMsg, _, _) -> Assert.True(false, errorMsg)

let test1 (p:Parser<'a,unit>) teststr parsed =
    match run p teststr with
    | Success(result, _, _)   -> Assert.True((parsed=result)
                                ,"parsed %A{parsed}, actual %A{result}")
    | Failure(errorMsg, _, _) -> Assert.True(false, errorMsg)

let checkIfParses  (p:Parser<'a,unit>) teststr =
    match run p teststr with
    | Success(result, _, _)   -> Assert.True(true,"F# is weird")
    | Failure(errorMsg, _, _) -> Assert.True(false, $"parsing failed with %s{errorMsg}")
    


[<Fact>]
let ``My test`` () =
    Assert.True(true)

[<Fact>]
let ``test pureText`` () = 
    test (pureText ["<";"/>"]) "abc<d" "abc"
    test (pureText ["<";"/>"]) "ab/>c<d" "ab"

[<Fact>]
let ``test enclosedIn`` () =
    test (enclosedIn "<" "/>") "<abc/>def" "<abc/>"

[<Fact>]
let ``test betweenNest`` () =
    // the regular (textBetween "\\<open>" "\\<close>") 
    // would stop in the first "\\<close>" tag and return
    test (betweenNest "<open>" "<close>")  
        "<open> sksks <open>enclosed <close> <close> abc"
        " sksks <open>enclosed <close> "

[<Fact>]
let ``test textBetween`` () =
    test (textBetween "<open>" "<close>") "<open> abcd <close> def" " abcd "

[<Fact>]
let ``test Isar comment`` () =
    test  comment "(* abc *)"  " abc "

[<Fact>]
let ``test parsing informal text`` () =
    test informalText 
        "text\\<open>some informal text with \\<open>embedded Isar\\<close>\\<close>"
        "some informal text with \\<open>embedded Isar\\<close>"

[<Fact>]
let ``test parsing section title`` () =
    test section
        "section\\<open>Abelian Group\\<close>"
        "Abelian Group"

[<Fact>]
let ``test notAnyOf combinator`` () =
    match run (notAnyOf [pstring "abc";pstring "def"]) "abdg" with
    | Success(result, _, _) -> Assert.Equal(result,())
    | Failure(errorMsg, _, _) -> Assert.True(false, errorMsg)

    // we expect the parser to fail here. Maybe we need to improve the
    // error message when it fails
    match run (notAnyOf [pstring "abc";pstring "def"]) "abcdg" with
    | Success(_, _, _) -> Assert.True(false, "notAnyOf succeeded unparsedly")
    | Failure(errorMsg, _, _) -> Assert.True(true,"notAnyOf should fail here")

[<Fact>]
let ``test alphaNumNotKeyword parser`` () =
    let p = alphaNumNotKeyword ['_']
    // this one should be ok, returning the string
    test p "ab1_def" "ab1_def"

    // parse until '?' which not on the list of allowed characters
    test p "ab1?def" "ab1"

    // fail because "ultimately" is a keyword
    match run p "ultimately" with
    | Success(_, _, _) -> Assert.True(false, "alphaNumNotKeyword succeeded unparsedly on " + "\"ultimately\"")
    | Failure(errorMsg, _, _) -> Assert.True(true,"alphaNumNotKeyword should fail here")
   
[<Fact>]
let ``test itemName`` () =
    test itemName "assms(3)" "assms(3)"

[<Fact>]
let ``test pureItemName`` () =
    test pureItemName "th_1.2(3)" "th_1.2"

[<Fact>]
let ``test varname`` () =
    test varname "\\<N>\\<^sub>0" "\\<N>\\<^sub>0" 

[<Fact>]
let ``test literalQuote`` () =
    test literalQuote "\\<open>x\\<in>B\\<close>" "`x\\<in>B`"

[<Fact>]
let ``test labelRef`` () =
    test labelRef "A1" "A1"
    test labelRef "\\<open>x+y=z\\<close>" "`x+y=z`"

[<Fact>]
let ``test parsing innnerText`` () =
    test innerText "\"x\\<in>A\"" "x\\<in>A"
    test innerText "?thesis" "?thesis"

[<Fact>]
let ``test incontext`` () =
    test incontext "(in topology0)" "topology0"

[<Fact>]
let ``test defnotation`` () =
    test defnotation "(infixl \"Xor\" 66)" "(infixl \"Xor\" 66)"
    test defnotation "(\"Net(_)\" 40)" "( \"Net(_)\" 40)"

[<Fact>]
let ``test defpreamble`` () =
    let teststr1 = "IsATopology (\"_ {is a topology}\" [90] 91) where"
    let parsed1 = ("","IsATopology","","( \"_ {is a topology}\" [90] 91)")
    test1 defpreamble teststr1 parsed1

    let teststr2 = "IsComplete (\"_ {is complete}\") where"
    let parsed2 = ("","IsComplete","","( \"_ {is complete}\" )")
    test1 defpreamble teststr2 parsed2

    let teststr3 = """IsTotal (infixl "{is total on}" 65) where"""
    let parsed3 = ("","IsTotal","","""(infixl "{is total on}" 65)""")
    test1 defpreamble teststr3 parsed3

[<Fact>]
let ``test labelsimp`` () =
    let teststr1 = "neut_def[simp]:"
    let parsed1 = ("neut_def",true)
    test1 labelsimp teststr1 parsed1

[<Fact>]
let ``test abbreviation`` () =
    let teststr = "abbreviation FilConvTop(\"_ \\<rightarrow>\\<^sub>F _ {in} _\")\n\
                    where \"\\<FF> \\<rightarrow>\\<^sub>F x {in} T \\<equiv> topology0.FilterConverges(T,\\<FF>,x)\""
    let parsed =  Abbr { abbname = "FilConvTop"; 
                            abbnotation = "_ \\<rightarrow>\\<^sub>F _ {in} _";
                            abbspec = "\\<FF> \\<rightarrow>\\<^sub>F x {in} T \\<equiv> topology0.FilterConverges(T,\\<FF>,x)" }            
    test1 abbreviation teststr parsed

[<Fact>]
let ``test definition`` () =
    let teststr = 
        """definition
IsTotal (infixl "{is total on}" 65) where
    "r {is total on} X \<equiv> (\<forall>a\<in>X.\<forall>b\<in>X. \<langle> a,b\<rangle> \<in> r \<or> \<langle> b,a\<rangle> \<in> r)" """
    let parsed = Def { defname = "IsTotal"
                        ; defcontext = ""
                        ; deftypespec = """(infixl "{is total on}" 65)"""
                        ; deflabel = ("",false)
                        ; def = "r {is total on} X \\<equiv> (\\<forall>a\\<in>X.\\<forall>b\\<in>X. \\<langle> a,b\\<rangle> \\<in> r \\<or> \\<langle> b,a\\<rangle> \\<in> r)"
                        }
    test1 definition teststr parsed


[<Fact>]
let ``test renamedvars`` () =
    let teststr = "K A M for K A M"
    let parsed:string list = ["K";"A";"M"]
    test1 renamedvars teststr parsed

[<Fact>]
let ``test inheritedFrom`` () =
    let teststr = "ring0 K A M for K A M +"
    let parsed = ("ring0",["K";"A";"M"])
    test1 inheritedFrom teststr parsed

[<Fact>]
let ``test namenotation`` () =
    let teststr = """grop (infixl "\<ra>" 90)"""
    let parsed = {fixedName = "grop"; fixedNotation = """infixl "\<ra>" 90"""}
    test1 namenotation teststr parsed

[<Fact>]
let ``test locItemfixes`` () =
    let teststr = "fixes P Q"
    let parsed = Fixes [{fixedName = "P";fixedNotation =""};
                        {fixedName = "Q"; fixedNotation =""}]

    test1 locItemfixes teststr parsed

[<Fact>]
let ``test locItemDefines`` () =
    let teststr = """defines csglistsum_def[simp]: "\<Sum>k \<equiv> Fold1(f,k)" """
    let parsed =  Defs {locdefNameSimp = ("csglistsum_def",true); locdef = """\<Sum>k \<equiv> Fold1(f,k)"""}
    test1 locItemDefines teststr parsed

[<Fact>]
let ``test statLabel`` () = 
    test statLabel "I:" "I"

[<Fact>]
let ``test labelledStatList`` () =
    let teststr = """A1: "a \<in> A"  "b \<in> B" """
    let parsed = ("A1",["a \\<in> A";"b \\<in> B"])
    test1 labelledStatList teststr parsed

[<Fact>]
let ``test listLabStatLists`` () =
    let teststr = """A1: "k \<in> nat"  "n \<in> nat" and A2: "k\<subseteq>n" """
    let parsed = [  ("A1",["k \\<in> nat" ;"n \\<in> nat"]);
                    ("A2",["k\\<subseteq>n"])
                    ]
    test1 listLabStatLists teststr parsed

[<Fact>]
let ``test locItemAssumes`` () =
    let teststr = """assumes isAbelian: "P {is commutative on} G" """
    let parsed = Assms [("isAbelian",["P {is commutative on} G"])]
    test1 locItemAssumes teststr parsed

[<Fact>]
let ``test localeItem`` () =
    let teststr = """defines AH_def [simp]: "AH \<equiv> AlmostHoms(G,P)" """
    let parsed = Defs {locdefNameSimp = ("AH_def",true); locdef = "AH \\<equiv> AlmostHoms(G,P)"  }
    test1 localeItem teststr parsed

[<Fact>]
let ``test locale`` () =
    let teststr = """locale group2 =
  fixes P 
  fixes dot (infixl "\<cdot>" 70)
  defines dot_def [simp]: "a \<cdot> b \<equiv> P`\<langle>a,b\<rangle>" """
    let locItems = [Fixes [{fixedName = "P"; fixedNotation = "" }];
                    Fixes [{fixedName = "dot"; fixedNotation = "infixl \"\\<cdot>\" 70" }];
                    Defs  {locdefNameSimp = ("dot_def",true); locdef = "a \\<cdot> b \\<equiv> P`\\<langle>a,b\\<rangle>"}
                    ]

    let parsed = Loc {localename = "group2"; 
            inheritsFrom = ("",[]);
            localeItems = locItems
            }
    test1 locale teststr parsed

[<Fact>]
let ``test parsing a subscript`` () =
    test subscript "\\<^sub>A" "A"

[<Fact>]
let ``test letstep`` () =
    let teststr = """let ?g = "{\<langle>m,\<mu> j. j\<in>A \<and> f`(j)=m\<rangle>. m\<in>B}" """
    let parsed = LetStep ("g","","{\\<langle>m,\\<mu> j. j\\<in>A \\<and> f`(j)=m\\<rangle>. m\\<in>B}")
    test1 letstep teststr parsed

[<Fact>]
let ``test fixstep`` () =
    let teststr = "fix M N"
    let parsed = FixStep ["M";"N"]
    test1 fixstep teststr parsed

[<Fact>]
let ``test next`` () =
    test1 next "next" Next 

[<Fact>]
let ``test locrefs`` () =
   let teststr1 = "from  A1 A2 \\<open>c\\<in>G\\<close>"
   let parsed1 = ["A1";"A2";"`c\\<in>G`"]
   test1 (locrefs "from") teststr1 parsed1

   let teststr2 = "with assms(3,4) I"
   let parsed2 = ["assms(3,4)";"I"]
   test1 (locrefs "with") teststr2 parsed2

[<Fact>]
let ``test parsing note`` () =
    let teststr = "note A1 \\<open>c\\<in>G\\<close>"
    let parsed = Note ["A1";"`c\\<in>G`"]
    test1 note teststr parsed

[<Fact>]
let ``test assume statement`` () =
    let teststr = "assume A: \"A \\<prec> csucc(m)\""
    let parsed = Assume [("A",["A \\<prec> csucc(m)"])]
    test1 assume teststr parsed

[<Fact>]
let ``test parsing a tactic`` () =
    test tactic "force" "force"

[<Fact>]
let ``test shortProofByTac`` () =
    let parsed = UsingBy { useunfold = ""; usedprops = []; useunfold1 = "";usedprops1 = []; ptactic = "auto" }
    test1 shortProofByTac "by auto" parsed

[<Fact>]
let ``test shortProofByRule`` () =
    let teststr = "by (rule group0_4_L8)"
    let parsed = ByRule "group0_4_L8"
    test1 shortProofByRule teststr parsed

[<Fact>]
let ``test anyOf`` () =
    let teststr = "def"
    let stream = new CharStream<unit>(teststr,0,3)
    let testss = ["abc";"def";"ghi"]
    let r = (anyOf testss) stream
    //the result should be teststr
    Assert.True(r.Status=Ok)
    Assert.Equal(r.Result,"def")
    // should not consume input
    let p = getPosition stream
    Assert.True(1L=p.Result.Line)
    Assert.True(1L=p.Result.Column)

[<Fact>]
let ``test shortProofRef`` () =
    let teststr = "using th1 th2 by simp"
    let parsed = ("using",["th1";"th2"])
    test1 shortProofRef teststr parsed

[<Fact>]
let ``test shortProofRefTac`` () =
    let teststr = "using group0_3_L2 assms(1) unfolding IsAnormalSubgroup_def by auto"
    let parsed = UsingBy { useunfold = "using"
                        ; usedprops = ["group0_3_L2";"assms(1)"]
                        ; useunfold1 = "unfolding"
                        ; usedprops1 = ["IsAnormalSubgroup_def"]
                        ; ptactic = "auto"}
    test1 shortProofRefTac teststr parsed

[<Fact>]
let ``test claimfalse`` () =
    test1 claimfalse "False" [("",["False"])]

[<Fact>]
let ``test parsing a proof`` () =
    let teststr1 = """proof -
  from A2 have T1: "b\<inverse>\<in>G" "a\<inverse>\<in>G" using inverse_in_group by auto
  with A1 show "b\<inverse>\<cdot>a\<inverse> = a\<inverse>\<cdot>b\<inverse>" using IsCommutative_def by simp
  with A2 show "(a\<cdot>b)\<inverse> = a\<inverse>\<cdot>b\<inverse>" using group_inv_of_two by simp
  from A2 T1 have "(a\<cdot>b\<inverse>)\<inverse> = (b\<inverse>)\<inverse>\<cdot>a\<inverse>" using group_inv_of_two by simp
  with A1 A2 T1 show "(a\<cdot>b\<inverse>)\<inverse> = a\<inverse>\<cdot>b" 
    using group_inv_of_inv IsCommutative_def by simp
qed"""
    checkIfParses proof teststr1
    let teststr2 = """proof -
  have "GroupInv(G,f) \<subseteq> G\<times>G" using GroupInv_def by auto
  moreover from A1 have
    "\<forall>x\<in>G. \<exists>!y. y\<in>G \<and> \<langle>x,y\<rangle> \<in> GroupInv(G,f)"
    using group0_def group0.group0_2_L4 GroupInv_def by simp
  ultimately show ?thesis using func1_1_L11 by simp
qed"""
    checkIfParses proof teststr2

    let teststr3 = """proof -
  from A2 groupAssum obtain c where I: "c \<in> G \<and> b\<cdot>c = \<one>" 
    using IsAgroup_def by auto
  then have "c\<in>G" by simp
  have "\<one>\<in>G" using group0_2_L2 by simp
  with A1 A2 I have "b\<cdot>g =  b\<cdot>(g\<cdot>(b\<cdot>c))"
    using group_op_closed group0_2_L2 group_oper_assoc 
    by simp
  also from  A1 A2 \<open>c\<in>G\<close> have "b\<cdot>(g\<cdot>(b\<cdot>c)) = b\<cdot>(g\<cdot>b\<cdot>c)"
    using group_oper_assoc by simp
  also from A3 A2 I have "b\<cdot>(g\<cdot>b\<cdot>c)= \<one>" using group0_2_L2 by simp
  finally show "b\<cdot>g = \<one>" by simp
qed"""
    checkIfParses proof teststr3

[<Fact>]
let ``test sublocale`` () =
    let teststr = """sublocale reals < field1 Reals Add Mul realadd realminus realsub realmul zero one two realsq ROrd
  using field1_is_valid by auto"""
    checkIfParses sublocale teststr

[<Fact>]
let ``test parsing a proposition`` () =
    let testr1 = """theorem EquivClass_1_T1: 
  assumes "equiv(A,r)"  "Congruent2(r,f)"
  shows "ProjFun2(A,r,f) : (A//r)\<times>(A//r) \<rightarrow> A//r"
  using assms EquivClass_1_L9 ProjFun2_def ZF_fun_from_total 
  by simp"""
    checkIfParses proposition testr1

    let testr2 = """theorem EquivClass_2_T2:
  assumes A1: "equiv(A,r)" and A2: "Congruent2(r,f)"
  and A3: "f {is associative on} A"
  shows "ProjFun2(A,r,f) {is associative on} A//r"
proof -
  let ?g = "ProjFun2(A,r,f)"
  from A1 A2 have 
    "?g \<in> (A//r)\<times>(A//r) \<rightarrow> A//r"
    using EquivClass_1_T1 by simp
  moreover from A1 A2 A3 have
    "\<forall>c1 \<in> A//r.\<forall>c2 \<in> A//r.\<forall>c3 \<in> A//r.
    ?g`\<langle>?g`\<langle>c1,c2\<rangle>,c3\<rangle> = ?g`\<langle>c1,?g`\<langle>c2,c3\<rangle>\<rangle>"
    using EquivClass_2_L2 by simp
  ultimately show ?thesis
    using IsAssociative_def by simp
qed"""
    checkIfParses proposition testr2

[<Fact>]
let ``test itemWdescription`` () =
    let testr1 = """text\<open>We will use the multiplicative notation for the group operation. To do this, we
  define a context (locale) that tells Isabelle
  to interpret $a\cdot b$ as the value of function $P$ on the pair 
  $\langle a,b \rangle$.\<close>

locale group2 =
  fixes P 
  fixes dot (infixl "\<cdot>" 70)
  defines dot_def [simp]: "a \<cdot> b \<equiv> P`\<langle>a,b\<rangle>"
"""
    checkIfParses itemWdescription testr1

    let teststr2 = """text\<open>The next abbreviation introduces notation where we want to specify the space where
  the net convergence takes place.\<close>

abbreviation NetConvTop("_ \<rightarrow>\<^sub>N _ {in} _")
  where "N \<rightarrow>\<^sub>N x {in} T \<equiv> topology0.NetConverges(T,N,x)"
"""
    checkIfParses itemWdescription teststr2

[<Fact>]
let ``test subsection`` () = 
    let teststr = """subsection\<open>Properties of enumerations\<close>

text\<open>In this section we prove basic facts about enumerations.\<close>

text\<open>A special case of the existence and uniqueess 
  of the order isomorphism for finite sets
  when the first set is a natural number.\<close>

lemma (in enums) ord_iso_nat_fin:  
  assumes "A \<in> FinPow(X)" and "n \<in> nat" and "A \<approx> n"
  shows "\<exists>!f. f \<in> ord_iso(n,Le,A,r)"
  using assms NatOrder_ZF_1_L2 linord nat_finpow_nat 
    fin_ord_iso_ex_uniq by simp
  
text\<open>An enumeration is an order isomorhism, a bijection, and a list.\<close>

lemma (in enums) enum_props: assumes "A \<in> FinPow(X)"
  shows 
  "\<sigma>(A) \<in> ord_iso(|A|,Le, A,r)"
  "\<sigma>(A) \<in> bij(|A|,A)"
  "\<sigma>(A) : |A| \<rightarrow> A"
proof -
  from assms have
    "IsLinOrder(nat,Le)" and "|A| \<in> FinPow(nat)" and  "A \<approx> |A|"
    using NatOrder_ZF_1_L2 card_fin_is_nat nat_finpow_nat 
    by auto
  with assms show "\<sigma>(A) \<in> ord_iso(|A|,Le, A,r)"
    using linord fin_ord_iso_ex_uniq singleton_extract 
      Enumeration_def by simp
  then show "\<sigma>(A) \<in> bij(|A|,A)" and "\<sigma>(A) : |A| \<rightarrow> A"
    using ord_iso_def bij_def surj_def
    by auto
qed"""

    checkIfParses subsection teststr

[<Fact>]
let ``test parsing a theory`` () =
    let teststr = """(* License *) 
section \<open>Order on natural numbers\<close>

theory NatOrder_ZF imports Nat_ZF_IML Order_ZF

begin

text\<open>This theory proves that $\leq$ is a linear order on $\mathbb{N}$.
  $\leq$ is defined in Isabelle's \<open>Nat\<close> theory, and
  linear order is defined in \<open>Order_ZF\<close> theory. 
  Contributed by Seo Sanghyeon.\<close>

subsection\<open>Order on natural numbers\<close>

text\<open>This is the only section in this theory.\<close>

text\<open>To prove that $\leq$ is a total order, we use a result on ordinals.\<close>

lemma NatOrder_ZF_1_L1:
  assumes "a\<in>nat" and "b\<in>nat"
  shows "a \<le> b \<or> b \<le> a"
proof -
  from assms have I: "Ord(a) \<and> Ord(b)"
    using nat_into_Ord by auto
  then have "a \<in> b \<or> a = b \<or> b \<in> a"
    using Ord_linear by simp
  with I have "a < b \<or> a = b \<or> b < a"
    using ltI by auto
  with I show "a \<le> b \<or> b \<le> a"
    using le_iff by auto
qed

text\<open>$\leq$ is antisymmetric, transitive, total, and linear. Proofs by
  rewrite using definitions.\<close>

lemma NatOrder_ZF_1_L2:
  shows
  "antisym(Le)"
  "trans(Le)"
  "Le {is total on} nat"
  "IsLinOrder(nat,Le)"
proof -
  show "antisym(Le)"
    using antisym_def Le_def le_anti_sym by auto
  moreover show "trans(Le)"
    using trans_def Le_def le_trans by blast
  moreover show "Le {is total on} nat"
    using IsTotal_def Le_def NatOrder_ZF_1_L1 by simp
  ultimately show "IsLinOrder(nat,Le)"
    using IsLinOrder_def by simp
qed

end
"""
    checkIfParses theoryParser teststr

[<Fact>]
let ``test skipUntilAfterDot`` () =
  Assert.Equal("def",skipUntilAfterDot "abc.def")
  Assert.Equal("abc",skipUntilAfterDot "abc")

[<Fact>]
let ``test uniquefy`` () =
  let expected = 
    "abc2 def abc1 abc0 ghi\n<div id=\"par_abc\" style=\"display:none\">3</div>"
  Assert.Equal(expected,uniquefy "abc" "abc def abc abc ghi")

[<Fact>]
let ``test uniquefyids`` () =
  let expected = "abc2 def1 abc1 def0 abc0 ghi\n<div id=\"par_abc\" style=\"display:none\">3</div>\n<div id=\"par_def\" style=\"display:none\">2</div>"
  Assert.Equal(expected,uniquefyids ["abc";"def"] "abc def abc def abc ghi")

[<Fact>]
let ``test replaceAll`` () = 
  let repls = [("abc","***");("abcd","####")]
  let testStr = "abc def ghi def abcd"
  let expected = "*** def ghi def ####"
  Assert.Equal(expected,replaceAll repls testStr)

[<Fact>]
let ``test appToParts`` () =
  // test appToParts by replacing multiple stars in a string with one
  let testf = (=)'*'
  let transf = fun _ -> ['*']
  let teststr = "abc*** def ghi ** *"
  let expected = "abc* def ghi * *"
  // we have to convert the string to a list and back:
  let res =  List.ofSeq teststr 
            |> appToParts testf transf
            |> List.map string 
            |> String.concat ""
  Assert.Equal(expected, res) 

[<Fact>]
let ``test converting predicate`` () =
  let predicate = Seq.zip "{is a topology}" (Seq.replicate 15 1) |> Seq.toList
  let converted = convPredicate 1 predicate
  let expected = Seq.zip "\\text{ is a topology }" (Seq.replicate 22 1) |> Seq.toList
  Assert.Equal<(char*int) list>(expected, converted) 

[<Fact>]
let ``test detecting set comprehensions`` () =
  let addLevel (level:int) (s:string) : (char*int) list =
    level |> Seq.replicate s.Length |> Seq.zip s |> Seq.toList

  let setcompr1 = "{x\<in>X. \<phi>(x)}" |> addLevel 1
  Assert.True(isSetCompr setcompr1)

  let setcompr2 = "{\<tau>\<^sub>1}" |> addLevel 1
  Assert.True(isSetCompr setcompr2)

  let notsetcomr = "{is a topology}" |> addLevel 1
  Assert.False(isSetCompr notsetcomr)

[<Fact>]
let ``test nestLevel`` () =
  //let testr = "c(d)f"
  //let expected = [('c',0);('(',1);('d',1);(')',1);('f',0)]
  let teststr = "ab(c(de)f)"
  let expected = [('a',0);('b',0);('(',1);('c',1);('(',2);('d',2);('e',2);(')',2);('f',1);(')',1)]
  let actual = nestLevel '(' ')' teststr
  //printfn "%A" expected
  //printfn "%A"  actual
  Assert.Equal<(char*int) list> (expected,actual) 

[<Fact>]
let ``test convBraces`` () =
  let teststr1 = "{x}"
  Assert.Equal("\\{x\\}", convBraces teststr1)

  let teststr2 = "{{x}.x\\<in>X}"
  Assert.Equal("""\{\{x\}.x\<in>X\}""", convBraces teststr2)

  let teststr3 = "{is a topology}"
  Assert.Equal("\\text{ is a topology }",convBraces teststr3)
  