#lang racket

(define ones (cons 1 (lambda () ones)))

(define naturals 
    (letrec 
        ([f (lambda(x) (cons x (lambda () (f (+ x 1)))))])
        (f 1)))

(define fibs 
    (letrec
        ([f (lambda(x y) (cons (+ x y) (lambda () (f y (+ x y)))))])
        (f 1 0)))

(define (first n promise) 
    (if (= n 0)
        (list)
        (append (list (car promise)) (first (- n 1) ((cdr promise)) ) )))

(define (squares promise) 
    (cons (* (car promise) (car promise)) (lambda () (squares ((cdr promise))))))

(define (my-delay fun)
    (mcons 0 fun))

(define (my-force prom)
    (if (= (mcar prom) 0)
        (mcdr prom)
        (begin (set-mcar! prom #t)
               (set-mcdr! prom ((mcdr prom)))
               (mcdr prom))))

(define-syntax sml 
    (syntax-rules(nil null tl ::)
        [(sml nil) null]
        [(sml null x) (null? x)]
        [(sml tl x) (cdr x)]
        [(sml hd x) (car x)]
        [(sml x :: y) (append (list x) y)]))

(define (partitions m n) 1)