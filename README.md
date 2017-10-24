chr-curry
=========

This package contains a library `CHR` which provides an implementation of
[Constraint Handling Rules](https://dtai.cs.kuleuven.be/CHR/) in Curry,
an interpreter for CHR rules based on the refined operational semantics of
Duck et al. (ICLP 2004), and a compiler into CHR(Prolog).

To use CHR(Curry), specify the CHR(Curry) rules in a Curry program,
load it, add module `CHR` and interpret or compile the rules
with `runCHR` or `compileCHR`, respectively. This can be done
in one shot with

    > cypm curry :l MyRules :add CHR :eval 'compileCHR "MyCHR" [rule1,rule2]' :q

The directory `examples` contains various CHR(Curry) example programs.


Documentation
-------------

The structure and implementation of the CHR library is described
in the following paper:

M. Hanus:
CHR(Curry): Interpretation and Compilation of Constraint Handling Rules in Curry
Proc. of the 17th International Symposium on Practical Aspects of
Declarative Languages (PADL 2015)
Springer LNCS 9131, pp. 74-89, 2015
[Online](http://dx.doi.org/10.1007/978-3-319-19686-2_6)
