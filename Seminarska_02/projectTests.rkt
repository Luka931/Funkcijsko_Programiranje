#lang racket

(require rackunit (prefix-in pr: "02-project.rkt"))

(define TRIGGER_WRONG_ARGUMENT (pr:triggered (pr:exception "trigger: wrong argument type")))


(define t (pr:true))
(define f (pr:false))
(test-case "Booleans"
    (check-equal? (pr:fri t) t "True results in true.")
    (check-equal? (pr:fri f) f "False results in flase.")
)

(define iPos (pr:int 12))
(define iNeg (pr:int -12))
(test-case "Integers"
    (check-equal? (pr:fri iPos) iPos "Positive intiger")
    (check-equal? (pr:fri iNeg) iNeg "Negative intiger")
)

(define listT (pr:.. iPos (pr:.. iNeg (pr:.. t (pr:.. f f)))))
(define seqT (pr:.. iPos (pr:.. iNeg (pr:.. t (pr:.. f (pr:empty))))))
(test-case "List, Sequence, and Empty"
    (check-equal? (pr:fri listT) listT "List is returned")
    (check-equal? (pr:fri (pr:empty)) (pr:fri (pr:empty)) "Empty is returned")
    (check-equal? (pr:fri seqT) seqT "Sequence is returned")
)

(define excpStr (pr:exception "My exception"))
(define excpInt (pr:exception 12))
(define excpFri.. (pr:exception listT))
(test-case "Exceptions"
    (check-equal? (pr:fri excpStr) excpStr "Exception with a String")
    (check-equal? (pr:fri excpInt) excpInt "Exception with an Int")
    (check-equal? (pr:fri excpFri..) excpFri.. "Exception with a List")
)

(define trigger1 (pr:trigger excpStr))
(define trigger2 (pr:trigger excpFri..))
(define trigger3 (pr:trigger (pr:int 12)))
(test-case "Triggers"
    (check-equal? (pr:fri trigger1) (pr:triggered excpStr) "String exception should be triggered")
    (check-equal? (pr:fri trigger2) (pr:triggered excpFri..) "List exception should be triggered")
    (check-equal? (pr:fri trigger3) TRIGGER_WRONG_ARGUMENT "Trigger wrong argument should be returned")
)

(define handle1 (pr:handle trigger1 trigger1 seqT))
(define handle2 (pr:handle trigger1 trigger2 seqT))
(define handle3 (pr:handle (pr:int 23) trigger1 seqT))
(test-case "Handles"
    (check-equal? (pr:fri handle1) seqT "Successfully handled exception.")
    (check-equal? (pr:fri handle2) (pr:triggered excpFri..) "Unsuccessfully handled exception.")
    (check-equal? (pr:fri handle3) TRIGGER_WRONG_ARGUMENT "Handled exception is not right format.")
)

(define intT (pr:int 43))
(define seqF (pr:exception "Lalala"))
(define badEx (pr:add "sd" "sdf"))
(define ite1 (pr:if-then-else t intT seqF))
(define ite2 (pr:if-then-else f intT seqF))
(define ite3 (pr:if-then-else t intT badEx))
(define ite4 (pr:if-then-else f badEx intT))
(test-case "If then else"
    (check-equal? (pr:fri ite1) intT "True branchworks")
    (check-equal? (pr:fri ite2) seqF "False branch works")
    (check-equal? (pr:fri ite3) intT "Code doesn't breake even though we have bad expresion in false branch.")
    (check-equal? (pr:fri ite4) intT "Code doesn't breake even though we have bad expresion in true branch.")  
)

(define int?t (pr:?int (pr:if-then-else t (pr:int 12) t)))
(define int?f (pr:?int (pr:if-then-else f (pr:int 12) t)))
(test-case "?int"
    (check-equal? (pr:fri int?t) (pr:true) "?int should return (true) for int.")
    (check-equal? (pr:fri int?f) (pr:false) "?int should return (false) for non int.")
)

(define true?t (pr:?bool (pr:if-then-else f (pr:int 12) t)))
(define false?t (pr:?bool (pr:if-then-else f (pr:int 12) f)))
(define bool?f (pr:?bool (pr:if-then-else t (pr:int 12) t)))
(test-case "?bool"
    (check-equal? (pr:fri true?t) (pr:true) "?bool should return (true) for (true)")
    (check-equal? (pr:fri false?t) (pr:true) "?bool should return (true) for (false)")
    (check-equal? (pr:fri bool?f) (pr:false) "?bool should return (false) for non bool.")
)

(define ..?t1 (pr:?.. (pr:if-then-else f (pr:int 12) (pr:.. (pr:int 1) (pr:int 1)))))  
(define ..?t2 (pr:?.. (pr:if-then-else f (pr:int 12) (pr:.. (pr:int 1) (pr:empty)))))
(define ..?f (pr:?.. (pr:if-then-else t (pr:int 12) (pr:.. (pr:int 1) (pr:int 1)))))
(test-case "?.."
    (check-equal? (pr:fri ..?t1) t "?.. should return (true) for ..")
    (check-equal? (pr:fri ..?t2) t "?.. should return (true) for seq")
    (check-equal? (pr:fri ..?f) f "?.. should return (false) for non ../seq.")
)

(define empty?t (pr:?empty (pr:empty)))
(define empty?f (pr:?empty (pr:int 99)))
(test-case "?empty"
    (check-equal? (pr:fri empty?t) t "?empty should be (true) for empty.")
    (check-equal? (pr:fri empty?f) f "?empty should be (false) for non empty.")
)

(define seq?t (pr:?seq (pr:.. iPos (pr:.. iPos(pr:.. iNeg (pr:empty))))))
(define seq?f1 (pr:?seq (pr:.. iPos (pr:.. iPos(pr:.. iNeg iNeg)))))
(define seq?f2 (pr:?seq iNeg))
(test-case "?seq"
    (check-equal? (pr:fri seq?t) t "?seq should be (true) for seq")
    (check-equal? (pr:fri seq?f1) f "?seq should be (false) for .. that doesn't end with (empty)")
    (check-equal? (pr:fri seq?f2) f "?seq should be (false) for non seq")
)

(define exception?t (pr:?exception (pr:exception "tralalala")))
(define exception?f (pr:?exception (pr:int "tralalala")))
(test-case "?exception"
    (check-equal? (pr:fri exception?t) t "?exception should be (true) for exception")
    (check-equal? (pr:fri exception?f) f "?exception should be (false) for non exception")
)

; (fri (vars "a" (int -12)
;     (add (valof "a")
;         (vars (list "a" "b") (list (int 12) (int 99)) (add (valof "a") (valof "b")))
;     )
; ))







