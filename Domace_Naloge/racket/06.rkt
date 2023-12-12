#lang racket

(define (power x n) 
  (if (= n 0)
  1
  (* x (power x (- n 1)))))

(define (gcd a b)
  (if (> a b)
    (gcd b a)
    (if (= a 0)
      b
      (gcd (remainder b a) a))))

(define (fibR n nth nth1)
  (if (= n 0)
    nth1
    (fibR (- n 1) nth1 (+ nth nth1))))

(define (fib n)
  (if (= n 1)
    1
    (fibR (- n 2) 1 1)
    ))

(define (reverse seq)
  (if (null? seq)
    (list )
    (append (reverse (cdr seq)) (list (car seq)))))

(define (remove x seq)
  (if (null? seq)
    (list )
    (if (equal? x (car seq))
      (remove x (cdr seq))
      (append (list (car seq)) (remove x (cdr seq))))))

(define (map fun seq)
  (if (null? seq)
    (list)
    (append (list (fun (car seq))) (map fun (cdr seq)))))

(define (filter fun seq)
  (if (null? seq)
    (list)
    (if (fun (car seq))
      (append (list (car seq)) (filter fun (cdr seq)))
      (filter fun (cdr seq)))))

(define (zip seq1 seq2)
  (if (or (null? seq1) (null? seq2))
    (list)
    (append (list (cons (car seq1) (car seq2))) (zip (cdr seq1) (cdr seq2)))))

(define (range start end n)
  (if (> start end)
    (list)
    (append (list start) (range (+ start n) end n))))

(define (is-palindrome seq)
  (null? (filter (lambda (x) (not x)) 
                 (map (lambda (pair) (= (cdr pair) (car pair))) 
                      (zip seq (reverse seq))))))