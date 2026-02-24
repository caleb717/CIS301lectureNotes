// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def lem(p: B): Unit = {
  Deduce(
    |- ( p | !p )
      Proof(
        //All theorems start with a subprofo
        //Only one that makes sense here is PbC
        1 SubProof( //PbC: Assume the negation of what you're trying to prove
          2 Assume (!(p | !p)),

          //NegI SubProof
          3 SubProof(
            4 Assume (p),
            5 (p | !p) by OrI1(4),
            6 (F) by NegE(5, 2)
            //Goal:F
          ),
          7 (!p) by NegI(3),
          8 (p | !p) by OrI2(7),

          9 (F) by NegE(8, 2),
          //Need (p | !p) to contradict with assume, try to start with (!p)
          //Goal: F
        ),
        10 (p | !p) by PbC(1),
        
  )
  )
}