Tyler Petrochko
CPSC 454 VCG Project
Acknowledgement: This project was originally created by Ruzica and Quentin.

My implementation can be built with the command "make". My benchmarks are
included in the "benchmarks/" directory.

The following four files should return "Valid"

    fiba.imp
    min.imp
    multa.imp
    sort3.imp

while

    brokenfind.imp

should return "Invalid". In order for this to run, the program "z3" must be
globally invokeable. To get a verbose output, use the "-v" flag. To change
the command used to invoke z3, edit line 9 of vcgen.scala:

  var z3dst = "z3"

to a more appropriate value.




