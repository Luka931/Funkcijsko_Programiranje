#lang racket

(struct int (int) #:transparent)
(struct true () #:transparent)
(struct false () #:transparent)
(struct .. (e1 e2) #:transparent)
(struct empty() #:transparent)
(struct exception(e) #:transparent)
(struct trigger(e) #:transparent)
(struct triggered(e) #:transparent)
(struct handle(e1 e2 e3) #:transparent)
(struct if-then-else(condition e1 e2) #:transparent)
(struct ?int(e) #:transparent)
(struct ?bool(e) #:transparent)
(struct ?..(e) #:transparent)
(struct ?seq(e) #:transparent)
(struct ?empty(e) #:transparent)
(struct ?exception(e) #:transparent)
(struct add(e1 e2) #:transparent)
(struct mul(e1 e2) #:transparent)
(struct ?leq(e1 e2) #:transparent)
(struct ?=(e1 e2) #:transparent)
(struct head(e) #:transparent)
(struct tail(e) #:transparent)
(struct ~(e) #:transparent)
(struct ?all(e) #:transparent)
(struct ?any(e) #:transparent)

; HelperFunctions for fri interpreter

(define (isBool? e)
    (or (true? e) (false? e)))

(define (isSeq? seq) (let*
    ([e2 (..-e2 seq)])
    (if (..? e2)
        (isSeq? e2)
        (empty? e2))))

(define (addInt e1 e2)
    (int (+ (int-int e1) (int-int e2))))

(define (addBool e1 e2)
    (if (and (false? e1) (false? e2))
        (false)
        (true)))

(define (addSeq seq1 seq2)(let* 
    ([e1 (..-e1 seq1)]
     [e2 (..-e2 seq1)])
    (if (empty? e2)
        (.. e1 seq2)
        (.. e1 (addSeq e2 seq2)))))

(define (mulInt e1 e2)
    (int (* (int-int e1) (int-int e2))))

(define (mulBool e1 e2)
    (if (and (true? e1) (true? e2))
        (true)
        (false)))

(define (intLeq? e1 e2)
    (<= (int-int e1) (int-int e2)))

(define (boolLeq? e1 e2)
    (if (and (false? e2) (true? e1))
        (false)
        (true)))

(define (..Len e)
    (if (not (..? (..-e2 e)))
         1
        (+ 1 (..Len (..-e2 e)))))

(define (seqLeq? e1 e2)
    (<= (..Len e1) (..Len e2)))

; All of the functions for Equalities

(define (exceptionEq? e1 e2) (let*
    ([e1Text (exception-e e1)]
     [e2Text (exception-e e2)])
    (string=? e1Text e2Text)))

(define (triggeredEq? e1 e2) (let*
    ([e1Ex (triggered-e e1)]
     [e2Ex (triggered-e e2)])
    (exceptionEq?  e1Ex e2Ex)))

(define (triggerEq? e1 e2)(let*
    ([e1Ex (trigger-e e1)]
     [e2Ex (trigger-e e2)])
    (exceptionEq?  e1Ex e2Ex)))

(define (intEq? e1 e2)
    (= (int-int e1) (int-int e2)))

(define (boolEq? e1 e2)
    (or (and (true? e1) (true? e2))
        (and (false? e1) (false? e2))))

(define (..Eq? e1 e2)(let* 
    ([e1e1 (..-e1 e1)]
     [e1e2 (..-e2 e1)]
     [e2e1 (..-e1 e2)]
     [e2e2 (..-e2 e2)]
     [firstsEq (universalEq? e1e1 e2e1)]
     [secondsEq (universalEq? e1e2 e2e2)])
    (if (or (string? firstsEq) (string? secondsEq))
        "Erorr"
    (if (and firstsEq secondsEq)
        #f
    (if (or (empty? e1e2) (empty? e2e2))
        #f
        "Erorr")))))

(define (universalEq? e1 e2)
    (if (and (int? e1) (int? e2))
        (intEq? e1 e2)
    (if (and (isBool? e1) (isBool? e2))
        (boolEq? e1 e2)
    (if (and (..? e1) (..? e2))
        (..Eq? e1 e2)
    (if (and (empty? e1) (empty? e2))
        #t
    (if (and (exception? e1) (exception? e2))
        (exceptionEq? e1 e2)
    (if (and (trigger? e1) (trigger? e2))
        (triggerEq? e1 e2)
    (if (and (triggered? e1) (triggered? e2))
        (triggeredEq? e1 e2)
        "Erorr"))))))))

(define (int~ e)
    (int (* -1 (int-int e))))

(define (bool~ e)
    (if (true? e)
        (false)
        (true)))

(define (seqContainsFalse? seq)(let* 
    ([e1 (..-e1 seq)]
     [e2 (..-e2 seq)])
    (if (false? e1)
        #t
    (if (empty? e2)
        #f
        (seqContainsFalse? e2)))))

(define (seqContainsAllFalse? seq)(let* 
    ([e1 (..-e1 seq)]
     [e2 (..-e2 seq)])
    (if (false? e1)
        (seqContainsAllFalse? e2)
    (if (empty? e2)
        #t
        #f))))
        


(define (fri e)
    (cond
        [(int? e) e]
        [(true? e) e]
        [(false? e) e]
        [(..? e) e]
        [(empty? e) e]
        [(exception? e) e]
        [(trigger? e) (letrec
            ([evaluated (fri (trigger-e e))])
            (if (exception? evaluated)
                (triggered evaluated)
                (triggered (exception "trigger: wrong argument type"))))]
        [(handle? e)(letrec
            ([e1 (fri (handle-e1 e))]
             [e2 (fri (handle-e2 e))]
             [e3 (handle-e3 e)])
            (begin
                [if (triggered? e1)
                     e1
                    (e1 (triggered (exception "trigger: wrong argument type")))]
                [if (triggeredEq? e1 e2)
                    (fri e3)
                    e2]))]
        [(if-then-else? e) (letrec
            ([condition (fri (if-then-else-condition e))]
             [e1 (if-then-else-e1 e)]
             [e2 (if-then-else-e2 e)])
            (if (true? condition)
                (fri e1)
                (fri e2)))]
        [(?int? e) (letrec
            ([evaluated (fri (?int-e e))])
            (if (int? evaluated)
                (true)
                (false)))]
        [(?bool? e) (letrec
            ([evaluated (fri (?bool-e e))])
            (if (isBool? evaluated)
                (true)
                (false)))]
        [(?..? e) (letrec
            ([evaluated (fri (?..-e e))])
            (if (..? evaluated)
                (true)
                (false)))]
        [(?empty? e)(letrec
            ([evaluated (fri (?empty-e e))])
            (if (empty? evaluated)
                (true)
                (false)))]
        [(?seq? e)(letrec
            ([evaluated (fri (?seq-e e))])
            (if (isSeq? evaluated)
                (true)
                (false)))]
        [(?exception? e)(letrec
            ([evaluated (fri (?exception-e e))])
            (if (exception? evaluated)
                (true)
                (false)))]
        [(add? e)(letrec
            ([e1 (fri (add-e1 e))]
             [e2 (fri (add-e2 e))])
            (if (and (int? e1) (int? e2))
                (addInt e1 e2)
            (if (and (isBool? e1) (isBool? e2))
                (addBool e1 e2)
            (if (and (isSeq? e1) (isSeq? e2))
                (addSeq e1 e2)
                (triggered (exception("add: wrong argument type")))))))]
        [(mul? e)(letrec
            ([e1 (fri (mul-e1 e))]
             [e2 (fri (mul-e2 e))])
            (if (and (int? e1) (int? e2))
                (mulInt e1 e2)
            (if (and (isBool? e1) (isBool? e2))
                (mulBool e1 e2)
                (triggered (exception("mul: wrong argument type"))))))]
        [(?leq? e)(letrec
            ([e1 (fri (?leq-e1 e))]
             [e2 (fri (?leq-e2 e))])
            (if (and (int? e1) (int? e2))
                (intLeq? e1 e2)
            (if (and (isBool? e1) (isBool? e2))
                (boolLeq? e1 e2)
            (if (and (isSeq? e1) (isSeq? e2))
                (seqLeq? e1 e2)
                (triggered (exception("?leq: wrong argument type")))))))]
        [(?=? e)(letrec
            ([e1 (fri (?=-e1 e))]
             [e2 (fri (?=-e2 e))]
             [result (universalEq? e1 e2)])
            (if (string? result)
                (triggered (exception("?leq: wrong argument type")))
                result))]
        [(head? e)
            (if (..? e)
                (..-e1 e)
            (if (empty? e)
                (triggered (exception("head: empty sequence")))
                (triggered (exception("head: wrong argument type")))))]

        [(tail? e)
            (if (..? e)
                (..-e2 e)
            (if (empty? e)
                (triggered (exception("tail: empty sequence")))
                (triggered (exception("tail: wrong argument type")))))]
        [(~? e)(letrec
            ([evaluated (fri (~-e e))])
            (if (isBool? evaluated)
                (bool~ evaluated)
            (if (int? evaluated)
                (int~ evaluated)
                (triggered (exception("~: wrong argument type"))))))]
        [(?all? e)(letrec
            ([evaluated (fri (?all-e e))])
            (if (isSeq? evaluated)
                (if (not (seqContainsFalse? evaluated))
                    (true)
                    (false))
                (triggered (exception("?all: wrong argument type")))))]
        [(?any? e)(letrec
            ([evaluated (fri (?any-e e))])
            (if (isSeq? evaluated)
                (if (not (seqContainsAllFalse? evaluated))
                    (true)
                    (false))
                (triggered (exception("?any: wrong argument type")))))]

        
        ))

