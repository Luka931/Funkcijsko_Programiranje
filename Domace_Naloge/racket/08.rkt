#lang racket

(struct int (int) #:transparent)  
(struct false () #:transparent)
(struct true () #:transparent)
(struct add(e1 e2) #:transparent)
(struct mul (e1 e2) #:transparent)
(struct ?leq (e1 e2) #:transparent)
(struct ?int (exp) #:transparent)
(struct if-then-else (c t f) #:transparent)

(define (intAdd e1 e2) (int (+ (int-int e1) (int-int e2))))
(define (isBool? e) (or (true? e) (false? e)))
(define (boolAdd e1 e2)
    (if (and (false? e1) (false? e2))
        (true)
        (if (or (false? e1) (false? e2))
            (false)
            (true))))
(define (intMul e1 e2) (int (* (int-int e1) (int-int e2))))
(define (boolMul e1 e2)
    (if (or (false? e1) (false? e2))
            (false)
            (true)))
(define (intLeq e1 e2)
    (if (<= (int-int e1) (int-int e2))
        (true)
        (false)))
(define (boolLeq e1 e2)
    (if (and (true? e1) (false? e2))
        (false)
        (true)))


(define (fri e)
    (cond
        [(int? e) e]
        [(true? e) e]
        [(false? e) e]
        [(add? e)
            (letrec 
                ([e1 (fri (add-e1 e))]
                 [e2 (fri (add-e2 e))])
                (if (and (int? e1) (int? e2))
                    (intAdd e1 e2)
                    (if (and (isBool? e1) (isBool? e2))
                        (boolAdd e1 e2)
                        (error "Invalide operands for add operator."))))]
        [(mul? e)
            (letrec 
                ([e1 (fri (mul-e1 e))]
                 [e2 (fri (mul-e2 e))])
                (if (and (int? e1) (int? e2))
                    (intMul e1 e2)
                    (if (and (isBool? e1) (isBool? e2))
                        (boolMul e1 e2)
                        (error "Invalide operands for mul operator."))))]
        [(?leq? e)
            (letrec 
                ([e1 (fri (?leq-e1 e))]
                 [e2 (fri (?leq-e2 e))])
                (if (and (int? e1) (int? e2))
                    (intLeq e1 e2)
                    (if (and (isBool? e1) (isBool? e2))
                        (boolLeq e1 e2)
                        (error "Invalide operands for ?leq operator."))))]
        [(?int? e)
            (letrec 
                ([exp (fri (?int-exp e))])
                (if (int? exp)
                    (true)
                    (false)))]
        [(if-then-else? e)
            (if (true? (if-then-else-c e))
                (fri (if-then-else-t e))
                (fri (if-then-else-f e)))]
        ))

(define (conditional args ...)
    (let ([xs (list args ...)])
         (if(= (length xs) 3)
                (if-then-else (car xs) (cadr xs) (caddr xs))
                (if (> (length xs) 3)
                    (if-then-else (car xs) (cadr xs)  (conditional (cddr xs)))
                    (error "Wrong number of parameters.")))))

(define (?geq e1 e2)
    (?leq e2 e1))
