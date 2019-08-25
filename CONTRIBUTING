## Style Guide for Contributors to IsarMathLib

This document describes the coding style used by the IsarMathLib project.

The primary objective of the coding style used by by the IsarMathLib project is readability. Any person familiar with the standard mathematical notation should be able to read and follow the proofs. With some effort from the coder, the Isar syntax can get very close to that goal. Here are the principles to follow, in the order of their importance:

1. Use only the declarative Isar style, no verification scripts using the old Isabelle style will be allowed in IsarMathlib.

2. Stay as close as you can to the natural language and standard mathematical notation. 

    Most of the steps in the proofs can be written in a form similar to
    
     `from <local facts> have <statement> using <theorems> by simp`

    I am sure many proofs in IsarMathLib can be shortened by doing some (erule_tac a=a in wf_on_induct, assumption, +blast intro! and I am not making this up) magic. We think a couple of additional lines of proof are worth it if we can avoid this low level ugliness. 
    This also concerns naming of the notions you define. Whenever practical, try not to use keywords or names that are not words. If you define the set of integers, don't call them "int", call them Integers. If you define real numbers, don't call them "double". 

3. Write comments with embedded LaTeX formulae.

    Comments should be written at the start of every theory file, every section, before every definition and theorem.
    The comments don't have to be very precise or long, but do need to provide some information. We hope that future proof browsers will allow to hyperlink the theorems referenced in the proof and show the comments. Also searching for theorems is easier to implement with the keywords in comments.
    However, creating an impression that the comments contain a paralel "informal proof" (an oxymoron) should be avoided.

4. Use locales to define notation. 
