![Verification badge](https://github.com/SKolodynski/IsarMathLib/actions/workflows/verification.yml/badge.svg)
![Style-Check badge](https://github.com/SKolodynski/IsarMathLib/actions/workflows/style-check.yml/badge.svg)

## What is this?

IsarMathLib is a library of formalized mathematics for Isabelle/ZF.

## Installation

[Isabelle](https://www.cl.cam.ac.uk/research/hvg/Isabelle/index.html) is a theorem proving environment developed at Cambridge University and TU Munich.
Isabelle needs to be installed on the machine before you can generate IsarMathLib proof documents or verify the proofs. The Isabelle site provides the installation instructions. IsarMathLib is always tested only with the version of Isabelle that is current at the time of IsarMathLib release.

IsarMathLib needs Isabelle/ZF logic that is not shipped precompiled in the Isabelle distribution bundle. To build the ZF heap go to the directory where you have unpacked Isabelle and type "./bin/isabelle build -b ZF". Alternatively, one can change the default logic in the etc/settings file from HOL to ZF and then start Isabelle environment with the main `Isabelle2024` executable script. This should start with building the ZF heap image.

Before processing the IsarMathLib project theories, make sure you have LaTeX installed (including extras, for example in Ubuntu run "apt-get install texlive-latex-extras").

Process the theory files with the "isabelle build -D ./IsarMathLib" command issued in the main project directory where this file is. Make sure the bin directory of the Isabelle distribution is in PATH environment variable, or provide the full path to isabelle executable located there. Checking the proofs will take a couple of minutes, but will eventually produce the proof document and outline and tell you where the the files are located.

## Readable presentations

The best place to start is the [isamathlib.org](http://www.isarmathlib.org/) site which provides an experimental HTML rendering of most of the IsarMathLib theories.

The Isabelle generated [proof document](https://skolodynski.github.io/IsarMathLib/IsarMathLib/document.pdf) contains all definitions and theorems with formally verified proofs from the last release. The [outline](https://skolodynski.github.io/IsarMathLib/IsarMathLib/outline.pdf) contains all theorems and comments, but does not contain the proofs. Isabelle generated HTML rendering can be browsed [here](https://skolodynski.github.io/IsarMathLib/IsarMathLib/index.html).


## Formalized mathematics projects

Here is a list of formalized mathematics projects I found on GitHub:

| Project                                                          | Proof assistant/Logic  |  Comment |
|------------------------------------------------------------------|:----------------------:|---------:|
| [Homotopy Type Theory in Agda](https://github.com/HoTT/HoTT-Agda)|  Agda                  |          |
| [Isabelle/HoTT](https://github.com/jaycech3n/Isabelle-HoTT)      |  Isabelle/HoTT         |          |
| [Lean mathlib](https://github.com/leanprover-community/mathlib)  |  Lean                  |see also the [paper](https://arxiv.org/abs/1910.09336) on arXiv |
| [Math](https://github.com/berenoguz/Math)                        |  Agda                  |          |
| [Mathematical Components](https://github.com/math-comp/math-comp)|  Coq                   |          |
| [Metamath Zero](https://github.com/digama0/mm0)                  |  Metamath Zero         |see also the [paper](https://arxiv.org/abs/1910.10703) on arXiv |
| [Odd Order](https://github.com/math-comp/odd-order)              |  Coq                   |a mechanization of the Odd Order Theorem|
| [set.mm](https://github.com/metamath/set.mm)                     |  Metamath/ZFC          |          |
| [isabelle-zf-experiments](https://github.com/alexkrauss/isabelle-zf-experiments)| Isabelle/ZF | superseded by [tyset](https://bitbucket.org/cezaryka/tyset/src/master/) |

