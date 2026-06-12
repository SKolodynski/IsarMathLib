# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Project Is

IsarMathLib is a library of formalized mathematics for Isabelle/Isar, built on top of Isabelle/ZF (Zermelo-Fraenkel set theory). All mathematical content lives in `.thy` (theory) files under `IsarMathLib/`. The project also includes `isar2html2.0/`, an F# tool that converts theory files to HTML for the isarmathlib.org website.

## Verification (Isabelle)

Isabelle is not a standard CLI tool — verification runs via Docker:

```bash
# Verify all theories
docker build -t isarmathlib .
docker run isarmathlib
```

The Dockerfile uses the base image `slawekkol/isarmathlib:isabelle-zf-2025-1` and runs `isabelle build -D /home/isabelle/IsarMathLib`. The `IsarMathLib/ROOT` file defines the session and lists theories in dependency order.

To verify a single theory locally, you need Isabelle installed and run:
```bash
isabelle build -D IsarMathLib -o "theories=TheoryName"
```

## Style Check (isar2html2.0)

The style checker parses theory files and enforces formatting rules:

```bash
docker build -f isar2html2.0/Dockerfile -t isar2html .
docker run isar2html
```

The F# tool (`isar2html2.0/`) can also be built locally with `dotnet build --configuration Release` inside `isar2html2.0/`.

## Theory File Architecture

Theories import each other — the dependency chain in `IsarMathLib/ROOT` reflects the build order:

- **Foundation**: `Fol1.thy`, `ZF1.thy` — extensions to Isabelle/ZF's FOL and set theory
- **Order/Functions**: `Order_ZF*.thy`, `func*.thy`, `NatOrder_ZF.thy`
- **Algebra (bottom-up)**: `Semigroup_ZF` → `Monoid_ZF` → `Group_ZF` → `AbelianGroup_ZF` → `Ring_ZF` → `Field_ZF` → `OrderedField_ZF`
- **Number systems**: `Int_ZF*.thy`, `Real_ZF*.thy`, `Complex_ZF.thy`
- **Topology**: `Topology_ZF*.thy`, `UniformSpace_ZF*.thy`, `MetricSpace_ZF*.thy`, `TopologicalGroup_ZF*.thy`
- **Metamath interface**: `MMI_*.thy`, `Metamath_Interface.thy` — bridges to Metamath theorem database

Numbered suffixes (e.g., `Group_ZF_1.thy`, `Group_ZF_2.thy`) indicate continuation files for the same topic.

## Coding Style (from CONTRIBUTING.md)

1. **Declarative Isar only** — no tactic scripts (no `apply`, `erule_tac`, `blast intro!` chains). Every proof step should look like:
   ```
   from <local facts> have <statement> using <theorems> by simp
   ```

2. **Natural language names** — use `Integers` not `int`, `TheNeutralElement` not `e`. Avoid non-word identifiers.

3. **Comments with embedded LaTeX** — required at the start of every theory file, every section, before every definition and theorem. Use `text\<open>...\<close>` blocks. Comments inform HTML rendering and search; they should not duplicate a full informal proof.

4. **Locales for notation** — algebraic structures are defined via Isabelle locales, grouping assumptions and notation together.

## isar2html Parser Rules

The `isar2html2.0` tool (`IMLParser.fs`) parses `.thy` files to produce HTML. A theory file **must** satisfy all of the following to parse successfully, or it won't appear on the website.

### Required structure

A theory file must follow this top-level shape exactly:

```
section\<open>...\<close>
theory Name imports ... begin
text\<open>...\<close>          ← theory intro (exactly one)
subsection\<open>...\<close>
text\<open>...\<close>          ← subsection intro (exactly one per subsection)
text\<open>...\<close> <item>   ← one text block before each formal item
...
end
```

- At least one `subsection\<open>...\<close>` block is required.
- **No space** between `text` and `\<open>` — `text\<open>` is correct; `text \<open>` fails.
- `subsection\<open>` also requires no space (parsed as a literal prefix string).
- `section` allows optional whitespace before `\<open>` but `subsection` does not.

### Supported formal items

The parser handles these top-level items inside a subsection (each must be preceded by a `text\<open>...\<close>` block):

- `definition`
- `abbreviation`
- `lemma` / `theorem` / `corollary`
- `locale`
- `sublocale`
- `interpretation`

`lemmas` is **not** a supported item and will cause a parse failure.

### Every formal item needs its own preceding `text` block

The subsection intro `text\<open>...\<close>` does **not** count as the item-preceding text. Every `definition`, `lemma`, etc. must have its own dedicated `text\<open>...\<close>` block immediately before it, even if it is the first item in a subsection.

### Lemmas must use explicit `shows`

The inline shorthand `lemma name: "statement"` is not accepted. Always use the explicit form:

```
lemma (in locale) name:
  shows "statement"
```

### Fact references: no `[OF ...]` or `[of ...]`

`itemName` in the parser only accepts characters matching `[A-Za-z0-9_.,()-]`. The `[` character is not allowed, so any fact instantiation like `lemma1[OF x]` or `foo[of a b]` appearing in `using`, `from`, or `with` clauses causes a parse failure.

**Fix**: introduce an intermediate `have` step:
```
(* instead of: using lemma1[OF x] *)
have h: ... using lemma1 by simp
... using h ...
```

### Proof Style Preferences

Avoid `interpret` in proofs. Instead, use `have ... using` steps with explicit locale theorems or unfold definitions directly. `interpret` creates locale instances mid-proof which obscures the proof structure and can be fragile.

## Variable Name Restrictions

The name `a` is reserved in Isabelle/ZF's inner syntax. Use descriptive variable names like `ltr`, `rtr`, `elem`, etc., to avoid parsing errors.

## Key Definitions Pattern

Predicates follow the `IsA*` naming convention:
- `IsAgroup(G,f)` — G is a group with operation f
- `IsAmonoid(G,f)` — G is a monoid
- `IsAtopology(T,\<tau>)` — T is a topology

The `TheNeutralElement(G,f)` construct uses Isabelle's definite description to extract the unique neutral element.
