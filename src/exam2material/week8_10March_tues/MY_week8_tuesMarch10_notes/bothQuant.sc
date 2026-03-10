// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ¬(∃ x P(x)) |- ∀ x ¬P(x)

@pure def bothQuant[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      |-
    (
      ∀((x: T) => !P(x))
    )
    Proof(
      1 ( !(∃((x: T) => P(x))) ) by Premise,

      //Top level of conclusion is "For all", so want AllI
      2 Let((a: T) => SubProof(
        //Next top level is !, so NegI
        3 SubProof(
          4 Assume (P(a)),
          5 (∃((x: T) => P(x))) by ExistsI[T](4),
          6 (F) by NegE(5, 1),
          //Goal: (F)  so we need ∃((x: T) => P(x)) to contradict premise
        ),
        7 (!P(a)) by NegI(3),
        //Goal: !P(a)
      )),
      8 (∀((x: T) => !P(x))) by AllI[T](2),

      //Goal:∀((x: T) => !P(x))
      
    )
  )
}