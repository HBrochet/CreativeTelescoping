## CreativeTelescoping

This is a Maple package to perform definite summation and integration by the method of *creative telescoping*. More precisely, it uses a variant called *reduction based* creative telescoping. The algorithms implemented in this package can be found in two articles. 

* For integrals: A. Bostan, F. Chyzak, P. Lairez, and B. Salvy, “Generalized Hermite Reduction, Creative Telescoping and Definite Integration of D-Finite Functions,” in *ISSAC’18—Proceedings of the 2018 ACM International Symposium on Symbolic and Algebraic Computation*, 2018, pp. 95–102. http://dl.acm.org/authorize?N667523 
* For sums: H. Brochet and B. Salvy, “Reduction-Based Creative Telescoping for Definite Summation of D-finite Functions”,  15 pages. Submitted. [https://arxiv.org/abs/2307.07216](https://arxiv.org/abs/2307.07216).

Contributors to the package include all the authors.

Open user_guide.mw in maple to see examples of how to use the package.

## Requirement
This package requires Mgfun to be installed:  Download the .mla file at  https://specfun.inria.fr/chyzak/mgfun.html and add it to the directory maple20XX/lib/.

## Installation
You can directly download the file CreativeTelescoping.mla from our github page or build it from the src folder using the makefile. Then add it to the directory directory maple20XX/lib/.

If the package is correctly installed you should be able to load it:

    with(CreativeTelescoping)


This package uses an internal function of the Mgfun package therefore at this stage it is needed to use the following command

    kernelopts(opaquemodules = false):

You can now open the user_guide.mw file located in the maple_worksheets folder to test your installation on real examples and to learn the syntax.
