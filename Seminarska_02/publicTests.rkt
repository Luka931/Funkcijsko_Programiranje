#lang racket
(require "02-project.rkt")

(require rackunit)
(require rackunit/text-ui)

(define all-tests
  (test-suite
   "pulic"
    
   (test-case
    "add 01"
    (check-equal?
     (add (mul (true) (true)) (false))
     (add (mul (true) (true)) (false))))
 
   (test-case
    "add 02"
    (check-equal?
     (fri (add (mul (true) (true)) (false)) null)
     (true)))

   (test-case
    "add 03"
    (check-equal?
     (fri (add (add (int 9) (int 9)) (true)) null)
     (triggered (exception "add: wrong argument type"))))

   (test-case
    "handle 01"
    (check-equal?
     (fri (handle (exception "add: wrong argument type")
                  (add (add (int 9) (int 9)) (true))
                  (false))
          null)
     (false)))
    
   (test-case
    "handle 02"
    (check-equal?
     (fri (handle (exception "fatal error")
                  (add (add (int 9) (int 9)) (true))
                  (false))
          null)
     (triggered (exception "add: wrong argument type"))))

   (test-case
    "handle 03"
    (check-equal?
     (fri (handle (exception "fatal error")
                  (add (add (int 9) (int 9)) (int -1))
                  (false))
          null)
     (int 17)))

   (test-case
    "handle 04"
    (check-equal? 
     (fri (handle (int 1337)
                  (add (add (int 9) (int 9)) (int -1))
                  (false))
          null)
     (triggered (exception "handle: wrong argument type"))))

   (test-case
    "handle 05"
    (check-equal? 
     (fri (handle (trigger (exception "fatal error"))
                  (add (add (int 9) (int 9)) (int -1))
                  (false))
          null)
     (triggered (exception "fatal error"))))

   (test-case
    "handle 06"
    (check-equal?
     (fri (handle (head (.. (exception "error") (int 10)))
                  (exception "error") (int 2)) null)
     (exception "error")))

   (test-case
    "handle 07"
    (check-equal?
     (fri (handle
           (exception "error")
           (trigger (exception "error"))
           (int 2)) null)
     (int 2)))
    
   (test-case
    "handle 08"
    (check-equal?
     (fri (handle
           (exception "error2")
           (handle (exception "error1")
                   (trigger (exception "error2"))
                   (int 2))
           (int 1)) null)
     (int 1)))

   (test-case
    "handle 09"
    (check-equal?
     (fri (handle (trigger (exception "error")) (int 1) (int 2)) null) 
     (triggered (exception "error"))))

   (test-case
    "handle 10"
    (check-equal?
     (fri (handle (exception "error") (int 1) (int 2)) null)
     (int 1)))

   (test-case
    "handle 11"
    (check-equal?
     (fri (handle (exception "error") (exception "error2") (int 2)) null)
     (exception "error2")))

   (test-case
    "handle 12"
    (check-equal?
     (fri (handle (exception "error") (exception "error") (int 2)) null)
     (exception "error")))

   (test-case
    "handle 13"
    (check-equal?
     (fri (handle (exception "error") (trigger (exception "error")) (int 2)) null)
     (int 2)))

   (test-case
    "handle 14"
    (check-equal? (fri (handle (exception "error2")
                               (trigger (exception "error")) (int 2)) null)
                  (triggered (exception "error"))))

   (test-case
    "tigger 15"
    (check-equal?
     (trigger (exception "test"))
     (trigger (exception "test"))))
   
   (test-case
    "tigger 16"
    (check-equal?
     (fri (trigger (exception "test")) null)
     (triggered (exception "test"))))


   (test-case
    "add forwarding the exception"
    (check-equal? 
     (fri (add (int 1) (trigger (exception "fatal error"))) null)
     (triggered (exception "fatal error"))))

   (test-case
    "trigger 01"
    (check-equal? 
     (fri (trigger (exception "fatal error")) null)
     (triggered (exception "fatal error"))))
   
   (test-case
    "trigger in trigger"
    (check-equal?
     (fri (trigger (trigger (exception "tra-la-la hop-sa-sa"))) null)
     (triggered (exception "tra-la-la hop-sa-sa"))))
    
   (test-case
    "?seq 01"
    (check-equal?
     (?seq (.. (int 1) (.. (int 2) (empty))))
     (?seq (.. (int 1) (.. (int 2) (empty))))))
    
   (test-case
    "?seq 02"
    (check-equal?
     (fri (.. (?seq (.. (int 1) (.. (int 2) (empty))))
              (?seq (.. (int 1) (.. (int 2) (int 3))))) null)
     (.. (true) (false))))

   (test-case
    "?seq 03"
    (check-equal?
     (?seq (empty))
     (?seq (empty))))

   (test-case
    "?seq 04"
    (check-equal?
     (fri (?seq (empty)) null)
     (true)))

   (test-case
    "add seq"
    (check-equal?
     (fri (add (.. (false) (empty))
               (.. (int 3) (empty))) null)
     (.. (false) (.. (int 3) (empty)))))

   (test-case
    "?.."
    (check-equal? (fri (?.. (empty)) null)
                  (false)))
  
   (test-case "add empty" (check-equal?
                           (fri (add (empty) (empty)) null)
                           (empty)))

    
   (test-case
    "join sequences"
    (check-equal?
     (fri (add
           (add
            (.. (int 1) (.. (int 2) (empty)))
            (.. (int -1) (.. (int -2) (empty))))
           (add
            (.. (int 11) (.. (int 21) (empty)))
            (.. (int -11) (.. (int -21) (empty)))))
          null)
     (..
      (int 1)
      (..
       (int 2)
       (..
        (int -1)
        (..
         (int -2)
         (..
          (int 11)
          (..
           (int 21)
           (.. (int -11) (.. (int -21) (empty)))))))))))

   (test-case
    "join sequences exception"
    (check-equal?
     (fri (add
           (.. (int 1) (int 2))
           (.. (int 3) (empty)))
          null)
     (triggered (exception "add: wrong argument type"))))

   (test-case
    "head 01"
    (check-equal?
     (fri (head (.. (add (.. (empty) (.. (empty) (empty)))
                         (empty))
                    (empty))) null)
     (.. (empty) (.. (empty) (empty)))))

   (test-case
    "head 02"
    (check-equal?
     (fri (head (head (.. (int 1) (false)))) null)
     (triggered (exception "head: wrong argument type"))))

   (test-case
    "tail 01"
    (check-equal?
     (fri (tail (.. (int 4) (int 9))) null)
     (int 9)))

   (test-case
    "tail 02"
    (check-equal?
     (fri (tail (.. (int 4) (empty))) null)
     (empty)))
    
   (test-case
    "tail 03"
    (check-equal? (fri (tail (empty)) null)
                  (triggered (exception "tail: empty sequence"))))

   (test-case
    "tail 04"
    (check-equal? (fri (tail (int 1)) null)
                  (triggered (exception "tail: wrong argument type"))))
 
   (test-case
    "vars 01"
    (check-equal?
     (fri (vars "a" (add (mul (int 1) (int 2)) (mul (int -3) (int 4)))
                (mul (valof "a") (valof "a"))) null)
     (int 100)))
    
   (test-case
    "vars 02"
    (check-equal?
     (fri (vars (list "a" "b")
                (list (mul (mul (int 1) (int 2)) (mul (int -3) (int 4)))
                      (~ (add (mul (int 1) (int 2)) (mul (int -3) (int 4)))))
                (add (valof "a") (valof "b"))) null)
     (int -14)))

   (test-case
    "vars 03"
    (check-equal?
     (fri (vars (list "s1" "s2" "s3")
                (list (.. (false) (true))
                      (.. (int 1) (int 2))
                      (.. (int 4) (int 4)))
                (mul (valof "s1") (mul (valof "s2") (valof "s3")))) null)
     (triggered (exception "mul: wrong argument type"))))
    
   (test-case
    "vars list 01"
    (check-equal?
     (fri (vars (list "a" "b" "c")
                (list (int 1) (int 2) (int 3))
                (fun "linear" (list "x1" "x2" "x3")
                     (add (mul (valof "a") (valof "x1"))
                          (add (mul (valof "b") (valof "x2"))
                               (mul (valof "c") (valof "x3")))))) null)
     (closure (list (cons "a" (int 1))(cons "b" (int 2)) (cons "c" (int 3)))
              (fun "linear" '("x1" "x2" "x3")
                   (add (mul (valof "a") (valof "x1"))
                        (add (mul (valof "b") (valof "x2"))
                             (mul (valof "c") (valof "x3"))))))))
    
   (test-case
    "call/fun recursive fibonacci"
    (check-equal?
     (fri (call
           (fun "fib" (list "n")
                (if-then-else
                 (?leq (valof "n") (int 2))
                 (int 1)
                 (add (call (valof "fib")
                            (list (add (valof "n") (int -1))))
                      (call (valof "fib")
                            (list (add (valof "n") (int -2)))))))
           (list (int 10))) null)
     (int 55)))

   (test-case
    "?all empty"
    (check-equal?
     (fri (?all (empty)) null)
     (true)))

   (test-case
    "?all exception"
    (check-equal?
     (fri (?all (.. (true) (false))) null)
     (triggered (exception "?all: wrong argument type"))))

   (test-case
    "?all exception"
    (check-equal?
     (fri (?all (.. (false) (.. (false) (int 1)))) null)
     (triggered (exception "?all: wrong argument type"))))

   (test-case
    "?any empty"
    (check-equal?
     (fri (?any (empty)) null)
     (false)))

   (test-case
    "?any exception"
    (check-equal?
     (fri (?any (.. (false) (.. (false) (int 1)))) null)
     (triggered (exception "?any: wrong argument type"))))
   
   (test-case
    "?all mix"
    (check-equal?
     (fri (?all
           (.. (true)
               (.. (?leq (false) (true))
                   (..
                    (?= (.. (int -19) (int 0))
                        (.. (head
                             (tail
                              (tail (add (.. (int 1) (empty))
                                         (.. (int 5) (.. (int -19) (empty)))))))
                            (int 0)))
                    (empty)))))
          null)
     (true)))
   
   (test-case
    "long-long"
    (check-equal?
     (fri
      (vars "a" (int 10)
            (vars (list "f" "g")
                  (list (fun "" (list "a" "b")
                             (add (valof "a") (mul (int 5) (valof "b"))))
                        (fun "" (list "c")
                             (add (valof "a") (valof "c"))))
                  (vars (list "a" "d" "g" "e")
                        (list (int 1)
                              (call (valof "g") (list (int -9)))
                              (fun "" (list "x")
                                   (add (valof "a")
                                        (mul (valof "x")
                                             (call (valof "f")
                                                   (list (int 1) (valof "a"))))))
                              (fun "" (list "f" "x")
                                   (call (valof "f") (list (valof "x")))))
                        (vars (list "fib" "test" "unit-fun" "proc")
                              (list (fun "fib" (list "n")
                                         (if-then-else
                                          (?leq (valof "n") (int 2))
                                          (int 1)
                                          (add (call (valof "fib")
                                                     (list (add (valof "n")
                                                                (int -1))))
                                               (call (valof "fib")
                                                     (list (add (valof "n")
                                                                (int -2)))))))
                                    (fun "" (list "x")
                                         (add (valof "x") (int 2)))
                                  
                                    (fun "" null
                                         (add (add (valof "a")
                                                   (valof "a"))
                                              (valof "a")))
                                  
                                    (proc ""
                                          (folding
                                           (fun "" (list "x" "acc")
                                                (mul (valof "x")
                                                     (valof "acc")))
                                           (int 1)
                                           (.. (valof "a")
                                               (.. (int 2)
                                                   (.. (int 3)
                                                       (.. (int 4)
                                                           (.. (call (valof "g")
                                                                     (list (int 5)))
                                                               (empty)))))))))
                              
                              
                              (.. (call (valof "unit-fun") null)
                                  (.. (call (valof "proc") null)
                                      (add (call (valof "g")
                                                 (list (add (int 5)
                                                            (call (valof "test")
                                                                  (list (int 3))))))
                                           (add (valof "d")
                                                (add (call (valof "f")
                                                           (list (int -1) (int -2)))
                                                     (add (valof "a")
                                                          (add (call (valof "fib")
                                                                     (list (int 5)))
                                                               (call (valof "e")
                                                                     (list (valof "test") (int 3))))))))))))))
      null)
     (.. (int 3) (.. (int 6360) (int 521)))))


   (test-case
    "binary"
    (check-equal?
     (fri (binary (add (int 10) (int 6))) null)
     (..
      (int 1)
      (..
       (int 0)
       (..
        (int 0)
        (.. (int 0) (.. (int 0) (empty))))))))

   (test-case
    "if-then-else"
    (check-equal?
     (fri (if-then-else (int 1) (int 2) (int 3)) null)
     (int 2)))

   (test-case
    "duplicate identifier -- you do NOT need to implement this"
    (check-equal?
     (fri (vars (list "a" "a" "a")
                (list (int 4) (int 5) (int 88))
                (valof "a")) null)
     (triggered (exception "vars: duplicate identifier"))))

   (test-case
    "duplicate argument identifier -- you do NOT need to implement this"
    (check-equal?
     (fri (fun "test" (list "a" "b" "c" "b") (int 1)) null)
     (triggered (exception "fun: duplicate argument identifier"))))

   (test-case
    "call 01"
    (check-equal?
     (fri (call (fun "test" (list "test") (valof "test")) (list (int 1))) null)
     (int 1)))

   (test-case
    "closure 01"
    (check-equal?
     (fri (call (fun "test" (list "t") (valof "test")) (list (int 1))) null)
     (closure '() (fun "test" '("t") (valof "test")))))

   (test-case
    "missing variable 01"
    (check-equal?
     (fri (vars (list "a" "b")
                (list (int 2) (mul (valof "a") (int 3)))
                (.. (valof "a") (valof "b"))) null)
     (triggered (exception "valof: undefined variable"))))

   (test-case
    "missing variable 02"
    (check-equal?
     (fri (vars (list "a" "b" "c")
                (list (int 1) (int 2) (int 3))
                (fun "linear" (list "x1" "x2" "x3")
                     (add (mul (valof "a") (valof "manjka"))
                          (add (mul (valof "b") (valof "x2"))
                               (mul (valof "c") (valof "x3")))))) null)
     (triggered (exception "closure: undefined variable"))))

   (test-case
    "procecudure exception"
    (check-equal?
     (fri (vars "a" (proc "" (int 1))
                (call (valof "a") (list (false)))) null)
     (triggered (exception "call: arity mismatch"))))

   (test-case
    "?bool forwarding the exception"
    (check-equal?
     (fri (?bool (add (true) (int 1))) null)
     (triggered (exception "add: wrong argument type"))))

   (test-case
    "prepending an empty sequence"
    (check-equal?
     (fri (add (empty) (.. (int -1) (empty))) null)
     (.. (int -1) (empty))))

   (test-case
    "?leq with invalid arguments"
    (check-equal?
     (fri (?leq (.. (int 1) (int 3)) (int 1)) null)
     (triggered (exception "?leq: wrong argument type"))))

   (test-case
    "?leq 01"
    (check-equal?
     (fri (?leq (empty) (empty)) null)
     (true)))

   (test-case
    "?leq 02"
    (check-equal?
     (fri (?leq (.. (int 10) (empty))
                (empty)) null)
     (false)))

   (test-case
    "vars exceptions"
    (check-equal?
     (fri (vars "a" (trigger (exception "t"))
                (trigger (exception "f"))) null)
     (triggered (exception "t"))))
 
   (test-case
    "missing variable"
    (check-equal?
     (fri (mul (valof "missing") (trigger (exception "e"))) null)
     (triggered (exception "valof: undefined variable"))))

   (test-case
    "call with invalid arguments"
    (check-equal?
     (fri (call (add (int 1) (int 2)) (list)) null)
     (triggered (exception "call: wrong argument type"))))

   (test-case
    "missing variable for closure"
    (check-equal?
     (fri (vars (list "a" "b" "c")
                (list (int 5) (int 2)
                      (fun "" (list) (valof "a")))
                (call (valof "c") (list))) null)
     (triggered (exception "closure: undefined variable"))))

   (test-case
    "mix"
    (check-equal?
     (fri (vars (list "a" "b" "c")
                (list (int 5) (int 2)
                      (fun "" (list) (exception "a")))
                (call (valof "c") (list))) null)
     (exception "a")))

   (test-case
    "calling with missing variable"
    (check-equal?
     (fri (vars (list "a" "b" "c")
                (list (int 5) (int 2)
                      (fun "" (list) (exception "a")))
                (call (valof "d") (list))) null)
     (triggered (exception "valof: undefined variable"))))

   (test-case
    "last element of the sequence via macro folding 01"
    (check-equal?
     (fri (folding
           (fun "" (list "x" "y")
                (valof "x"))
           (exception "empty list")
           (.. (int 1) (.. (int 2) (.. (int 3) (empty)))))
          null)
     (int 3)))

   (test-case
    "last element of the sequence via macro folding 02"
    (check-equal?
     (fri (folding
           (fun "" (list "x" "y")
                (valof "x"))
           (exception "empty list")
           (empty))
          null)
     (exception "empty list")))

   (test-case
    "concatination of sequences"
    (check-equal?
     (fri (rev (add (add (.. (int 2) (.. (int 3) (empty)))
                         (add (.. (int 2) (empty)) (empty)))
                    (add (.. (int 3) (empty)) (.. (empty) (empty))))) null)
     (.. (empty) (.. (int 3) (.. (int 2) (.. (int 3) (.. (int 2) (empty))))))))

   (test-case
    "genearting list with procedures"
    (check-equal?
     (fri (vars (list "s" "l") (list (int 4) (empty))
                (call
                 (proc "mklist"
                       (if-then-else
                        (?leq (int 0) (valof "s"))
                        (vars (list "s" "l")
                              (list (add (int -1) (valof "s"))
                                    (.. (valof "s") (valof "l")))
                              (call (valof "mklist") (list)))
                        (valof "l"))) (list)))
          null)
     (.. (int 0) (.. (int 1) (.. (int 2) (.. (int 3) (.. (int 4) (empty))))))))


   (test-case
    "good closure"
    (check-equal?
     (fri
      (vars "?" (int 1001)
            (vars "f"
                  (fun "" (list "x")
                       (mul (valof "x") (valof "?")))
                  (vars "?" (int -5)
                        (call (valof "f") (list (valof "?"))))))
      null)
     (int -5005)))

   
   (test-case
    "simple closure optimization"
    (check-equal?
     (fri (vars (list "a" "b" "c" "d")
                (list (int 1) (int 2) (int 3) (int 4))
                (fun "linear" (list "x1" "x2" "x3" "b")
                     (add (mul (vars "a" (int 0) (valof "a")) (valof "d"))
                          (add (mul (valof "b") (valof "x2"))
                               (mul (vars "c" (int 0) (valof "c")) (valof "x3")))))) null)
     (closure
      (list (cons "d" (int 4)))
      (fun
       "linear"
       '("x1" "x2" "x3" "b")
       (add
        (mul (vars "a" (int 0) (valof "a")) (valof "d"))
        (add
         (mul (valof "b") (valof "x2"))
         (mul (vars "c" (int 0) (valof "c")) (valof "x3"))))))))

   (test-case
    "vars + proc"
    (check-equal?
     (fri (vars (list "a" "b" "c")
                (list (int 5) (int 2)
                      (proc "" (valof "a")))
                (call (valof "c") (list))) null)
     (int 5)))

   (test-case
    "nested vars + fun"
    (check-equal?
     (fri (vars "a" (int 5)
             (vars (list "b" "c")
                   (list (int 2)
                         (fun "" (list) (valof "a")))
                   (call (valof "c") (list))))
       null)
     (int 5)))
   ))

(run-tests all-tests)