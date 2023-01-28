This tool is now obsolete, replaced by [isar2html2.0](https://github.com/SKolodynski/IsarMathLib/tree/master/isar2html2.0).

Isar2html is a Mathematical Knowledge Management 
tool for converting IsarMathLib sources to HTML. The inputs to the program are as follows:

  * A file called theories.conf with the list of theories to process.

  * The Isabelle theory files listed in theories.conf

  *  A file called isar2html_template.html.
  This is a template of a converted theory file. 

The result of the conversion can be viewed at the [isarmathlib.org](http://isarmathlib.org) site. 

The tool is written in Haskell and can be compiled with

```
cabal build
```


