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
(struct vars(s e1 e2) #:transparent)
(struct valof(s) #:transparent)
(struct fun(name farg body) #:transparent)
(struct proc(name body) #:transparent)
(struct closure(env f) #:transparent)
(struct call(e args) #:transparent)
(struct rVars(s e1 e2) #:transparent)
(struct rValof(s) #:transparent)
(struct recFuns(funs e1) #:transparent)

; HelperFunctions for fri interpreter

(define (isBool? e)
    (or (true? e) (false? e)))

(define (isSeq? seq) 
    (if (empty? seq)
        #t 
    (if (..? seq) 
        (let*
        ([e2 (..-e2 seq)])
        (if (..? e2)
            (isSeq? e2)
            (empty? e2)))
        #f)))

(define (addInt e1 e2)
    (int (+ (int-int e1) (int-int e2))))

(define (addBool e1 e2)
    (if (and (false? e1) (false? e2))
        (false)
        (true)))

(define (addSeq seq1 seq2)
    (if (empty? seq1)
        seq2
    (if (empty? seq2)
        seq1
        (.. (..-e1 seq1) (addSeq (..-e2 seq1) seq2)))))

(define (mulInt e1 e2)
    (int (* (int-int e1) (int-int e2))))

(define (mulBool e1 e2)
    (if (and (true? e1) (true? e2))
        (true)
        (false)))

(define (intLeq? e1 e2)
    (if (<= (int-int e1) (int-int e2))
        (true)
        (false)))

(define (boolLeq? e1 e2)
    (if (and (false? e2) (true? e1))
        (false)
        (true)))

(define (..Len e)
    (if (empty? e)
        0
    (if (not (..? (..-e2 e)))
        1
        (+ 1 (..Len (..-e2 e))))))

(define (seqLeq? e1 e2)
    (if (<= (..Len e1) (..Len e2))
        (true)
        (false)))

(define (int~ e)
    (int (* -1 (int-int e))))

(define (bool~ e)
    (if (true? e)
        (false)
        (true)))

(define (seqContainsFalse? seq)
    (if (empty? seq)
        #f
    (if (false? (..-e1 seq))
        #t
        (seqContainsFalse? (..-e2 seq)))))

(define (seqContainsAllFalse? seq)
    (if (empty? seq)
        #t
    (if (false? (..-e1 seq))
        (seqContainsAllFalse? (..-e2 seq))
        #f)))

(define (allUnique seq)
    (if (or (null? seq) (= (length seq) 1))
        #t
    (let ([hd (car seq)]
          [tl (cdr seq)])
    (if (member hd tl)
        #f
    (allUnique tl)))))

(define (expandEnvOne env s e1)(letrec
    ([exists (assoc s env)])
    (if (triggered? e1)
        e1
        (append (remove exists env) (list (cons s e1))))))

(define (expandEnvSeq env s e1)(let 
    ([newEnv (if (or (null? s) (null? e1)) 
              env
              (expandEnvOne env (car s) (car e1)))])
    (if (or (null? s) (null? e1) (triggered? newEnv))
        newEnv
        (expandEnvSeq newEnv (cdr s) (cdr e1))
    )))

(define (expandEnvironment env s e1)
    (if (and (list? s) (list? e1) (= (length s) (length e1)))
        (if (allUnique s)
            (expandEnvSeq env s e1)
            (triggered (exception "vars: duplicate identifier")))
    (if (and (string? s) (not (list? e1)))
        (expandEnvOne env s e1)
        (triggered (exception "vars: number of variables and values don't match")))))

(define (evaluateVars e1 env)
    (if (list? e1)
        (letrec 
            ([evaluated (map (lambda (x) (if (closure? x) x (fri x env))) e1)])
            (if (ormap triggered? evaluated)
                (findf triggered? evaluated)
                evaluated))
        (fri e1 env)))

(define (zip a b)
  (apply map list (list a b)))

(define (externalVars env e)
    (cond
        [(int? e) null]
        [(true? e) null]
        [(false? e) null]
        [(..? e) 
            (append (externalVars env (..-e1 e)) 
                    (externalVars env (..-e2 e)))]
        [(empty? e) null]
        [(exception? e) null]
        [(trigger? e) (externalVars env (trigger-e e))]
        [(handle? e)
            (append (externalVars env (handle-e1 e)) 
            (append (externalVars env (handle-e2 e))
                    (externalVars env (handle-e3 e))))]
        [(if-then-else? e)
            (append (externalVars env (if-then-else-condition e)) 
            (append (externalVars env (if-then-else-e1 e))
                    (externalVars env (if-then-else-e2 e))))]
        [(?int? e)
            (externalVars env (?int-e e))]
        [(?bool? e)
            (externalVars env (?bool-e e))]
        [(?..? e)
            (externalVars env (?..-e e))]
        [(?seq? e)
            (externalVars env (?seq-e e))]
        [(?empty? e)
            (externalVars env (?empty-e e))]
        [(?exception? e)
            (externalVars env (?exception-e e))]
        [(add? e)
            (append (externalVars env (add-e1 e))
                    (externalVars env (add-e2 e)))]
        [(mul? e)
            (append (externalVars env (mul-e1 e))
                    (externalVars env (mul-e2 e)))]
        [(?leq? e)
            (append (externalVars env (?leq-e1 e))
                    (externalVars env (?leq-e2 e)))]
        [(?=? e)
            (append (externalVars env (?=-e1 e))
                    (externalVars env (?=-e2 e)))]
        [(head? e)
            (externalVars env (head-e e))]
        [(tail? e)
            (externalVars env (tail-e e))]
        [(~? e)
            (externalVars env (~-e e))]
        [(?all? e)
            (externalVars env (?all-e e))]
        [(?any? e)
            (externalVars env (?any-e e))]
        [(vars? e)(letrec
            ([s (vars-s e)]
             [e1 (vars-e1 e)]
             [e2 (vars-e2 e)])
            (if (list? s)
                (append (apply append (map (lambda (x) (externalVars env x)) e1))
                        (externalVars (expandEnvironment env s e1) e2))
                (append (externalVars env e1)
                        (externalVars (expandEnvironment env s e1) e2))))]
        [(valof? e)(letrec
            ([s (valof-s e)]
             [value (assoc s env)])
            (if value
                null
                (list s)))]
        [(fun? e)(letrec
            ([name (fun-name e)]
             [farg (fun-farg e)]
             [body (fun-body e)])
            (externalVars (expandEnvironment (expandEnvironment env name body) farg (range 0 (length farg)))
                          body))]
        [(proc? e) null]
        [(call? e)
            (if (fun? (call-e e))(letrec
                ([name (fun-name (call-e e))]
                 [body (fun-body (call-e e))]
                 [farg (fun-farg (call-e e))]
                 [args (call-args e)])
                (append (externalVars (expandEnvironment (expandEnvironment env name body) farg args)
                                      body)
                        (apply append (map (lambda (x) (externalVars env x)) args))))
            (if (proc? (call-e e))(letrec
                ([body (proc-body (call-e e))]
                 [name (proc-name (call-e e))])
                (externalVars (expandEnvironment env name body) body))
            (if (valof? (call-e e))(letrec
                ([name (valof-s (call-e e))]
                 [getValue (assoc name env)]
                 [args (call-args e)])
                (if getValue
                    (externalVars env (call (cdr getValue) args))
                    (list name)))
                null)))]
        [(rVars? e)(letrec
            ([s (rVars-s e)]
             [e1 (rVars-e1 e)]
             [e2 (rVars-e2 e)])
            (if (list? s)
                (append (apply append (map (lambda (x) (externalVars env x)) e1))
                        (externalVars (expandEnvironment env s e1) e2))
                (append (externalVars env e1)
                        (externalVars (expandEnvironment env s e1) e2))))]
        [#t null]))

(define (keepOnlyNeeded env neededVars)
    (filter (lambda (x) (member (car x) neededVars)) env))

(define (optimizeEnv env neededVars)(letrec
    ([filteredEnv (keepOnlyNeeded env neededVars)])
    (if (= (length filteredEnv) (length (remove-duplicates neededVars)))
        filteredEnv
        (triggered (exception "closure: undefined variable")))))

(define rEnv (make-hash))

(define (fri e env)
    (cond
        [(int? e) e]
        [(true? e) e]
        [(false? e) e]
        [(..? e) (letrec
            ([e1 (fri (..-e1 e) env)]
             [e2 (fri (..-e2 e) env)])
            (if (triggered? e1)
                e1
            (if (triggered? e2)
                e2
                (.. e1 e2))))]
        [(empty? e) e]
        [(exception? e) e]
        [(trigger? e) (letrec
            ([evaluated (fri (trigger-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (exception? evaluated)
                (triggered evaluated)
                (triggered (exception "trigger: wrong argument type")))))]
        [(handle? e)(letrec
            ([e1 (fri (handle-e1 e) env)]
             [e2 (fri (handle-e2 e) env)]
             [e3 (handle-e3 e)])
            (if (triggered? e1)
                e1
            (if (not (exception? e1))
                (triggered (exception "handle: wrong argument type"))
            (if (equal? (triggered e1) e2)
                (fri e3 env)
                e2))))]
        [(if-then-else? e) (letrec
            ([condition (fri (if-then-else-condition e)  env)]
             [e1 (if-then-else-e1 e)]
             [e2 (if-then-else-e2 e)])
            (if (triggered? condition)
                condition
            (if (false? condition)
                (fri e2 env)
                (fri e1 env))))]
        [(?int? e) (letrec
            ([evaluated (fri (?int-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (int? evaluated)
                (true)
                (false))))]
        [(?bool? e) (letrec
            ([evaluated (fri (?bool-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (isBool? evaluated)
                (true)
                (false))))]
        [(?..? e) (letrec
            ([evaluated (fri (?..-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (..? evaluated)
                (true)
                (false))))]
        [(?empty? e)(letrec
            ([evaluated (fri (?empty-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (empty? evaluated)
                (true)
                (false))))]
        [(?seq? e)(letrec
            ([evaluated (fri (?seq-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (isSeq? evaluated)
                (true)
                (false))))]
        [(?exception? e)(letrec
            ([evaluated (fri (?exception-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (exception? evaluated)
                (true)
                (false))))]
        [(add? e)(letrec
            ([e1 (fri (add-e1 e) env)]
             [e2 (fri (add-e2 e) env)])
            (if (triggered? e1)
                e1
            (if (triggered? e2)
                e2
            (if (and (int? e1) (int? e2))
                (addInt e1 e2)
            (if (and (isBool? e1) (isBool? e2))
                (addBool e1 e2)
            (if (and (isSeq? e1) (isSeq? e2))
                (addSeq e1 e2)
                (triggered (exception "add: wrong argument type"))))))))]
        [(mul? e)(letrec
            ([e1 (fri (mul-e1 e) env)]
             [e2 (fri (mul-e2 e) env)])
            (if (triggered? e1)
                e1
            (if (triggered? e2)
                e2
            (if (and (int? e1) (int? e2))
                (mulInt e1 e2)
            (if (and (isBool? e1) (isBool? e2))
                (mulBool e1 e2)
                (triggered (exception "mul: wrong argument type")))))))]
        [(?leq? e)(letrec
            ([e1 (fri (?leq-e1 e) env)]
             [e2 (fri (?leq-e2 e) env)])
            (if (triggered? e1)
                e1
            (if (triggered? e2)
                e2
            (if (and (int? e1) (int? e2))
                (intLeq? e1 e2)
            (if (and (isBool? e1) (isBool? e2))
                (boolLeq? e1 e2)
            (if (and (isSeq? e1) (isSeq? e2))
                (seqLeq? e1 e2)
                (triggered (exception "?leq: wrong argument type"))))))))]
        [(?=? e)(letrec
            ([e1 (fri (?=-e1 e) env)]
             [e2 (fri (?=-e2 e) env)])
            (if (triggered? e1)
                e1
            (if (triggered? e2)
                e2
            (if (equal? e1 e2)
                (true)
                (false)))))]
        [(head? e)(letrec
            ([evaluated (fri (head-e e) env)])
            (if (..? evaluated)
                (..-e1 evaluated)
            (if (empty? evaluated)
                (triggered (exception "head: empty sequence"))
                (triggered (exception "head: wrong argument type")))))]
        [(tail? e)(letrec
            ([evaluated (fri (tail-e e) env)])
            (if (..? evaluated)
                (..-e2 evaluated)
            (if (empty? evaluated)
                (triggered (exception "tail: empty sequence"))
                (triggered (exception "tail: wrong argument type")))))]
        [(~? e)(letrec
            ([evaluated (fri (~-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (isBool? evaluated)
                (bool~ evaluated)
            (if (int? evaluated)
                (int~ evaluated)
                (triggered (exception "~: wrong argument type"))))))]
        [(?all? e)(letrec
            ([evaluated (fri (?all-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (isSeq? evaluated)
                (if (not (seqContainsFalse? evaluated))
                    (true)
                    (false))
                (triggered (exception "?all: wrong argument type")))))]
        [(?any? e)(letrec
            ([evaluated (fri (?any-e e) env)])
            (if (triggered? evaluated)
                evaluated
            (if (isSeq? evaluated)
                (if (not (seqContainsAllFalse? evaluated))
                    (true)
                    (false))
                (triggered (exception "?any: wrong argument type")))))]
        [(vars? e)(letrec
            ([s (vars-s e)]
             [e1 (evaluateVars (vars-e1 e) env)]
             [e2 (vars-e2 e)]
             [newEnv (if (triggered? e1) e1 (expandEnvironment env s e1 ))])
            (if (triggered? newEnv)
                  newEnv
                  (fri e2  newEnv)))]
        [(valof? e)(let
            ([value (assoc (valof-s e) env)])
            (if value
                (cdr value)
                (triggered (exception "valof: undefined variable"))))]
        [(fun? e)(letrec
            ([farg (fun-farg e)])
            (if (allUnique farg)
                (letrec
                    ([eV (externalVars null e)]
                     [newEnv (optimizeEnv env eV)])
                    (if (triggered? newEnv)
                        newEnv
                        (closure newEnv e)))
                (triggered (exception "fun: duplicate argument identifier"))))]
        [(proc? e) e]
        [(call? e)(letrec
            ([args (map (lambda (e) (fri e env)) (call-args e))]
             [clOrProc (fri (call-e e) env)])
            (if (triggered? clOrProc)
                clOrProc
            (if (closure? clOrProc)(letrec
                ([envFun (closure-env clOrProc)]
                 [farg (fun-farg (closure-f clOrProc))]
                 [body (fun-body (closure-f clOrProc))]
                 [name (fun-name (closure-f clOrProc))])
                (if (= (length args) (length farg))
                    (fri body (expandEnvironment (expandEnvironment envFun name clOrProc) farg args))
                    (triggered (exception "call: arity mismatch"))))
            (if (proc? clOrProc)(letrec
                ([name (proc-name clOrProc)]
                 [body (proc-body clOrProc)])
                (if (= (length args) 0)
                    (fri body (expandEnvironment env name clOrProc))
                    (triggered (exception "call: arity mismatch"))))
            (if (rValof? clOrProc)
                (fri (call clOrProc args) env)
                (triggered (exception "call: wrong argument type"))
            )))))]
        [(rVars? e)(letrec
            ([s (rVars-s e)]
             [e1 (evaluateVars (rVars-e1 e) env)]
             [e2 (rVars-e2 e)])
            (if (triggered? e1)
                  e1
                  (begin 
                  (for-each (lambda (x) (hash-set! rEnv (first x) (second x))) (zip s e1))
                  (fri e2 env))))]
        [(rValof? e)
            (hash-ref rEnv (rValof-s e) (triggered(exception "rValof: Real variable with this name does not exist")))]
        [(recFuns? e)
        (if (and (list? (recFuns-funs e)) (andmap fun? (recFuns-funs e)))
            (letrec
                ([funs (recFuns-funs e)]
                 [funNames (map (lambda (x) (fun-name x)) funs)]
                 [e1 (recFuns-e1 e)]
                 [newEnv (expandEnvironment env funNames (map (lambda (x) (rValof x)) funNames))]
                 [closures (map (lambda (x) (fri x newEnv)) funs)])
                (begin
                (for-each (lambda (x) (hash-set! rEnv (first x) (second x))) (zip funNames closures))
                (fri e1 newEnv)))
            (triggered(exception "recFuns: wrong argument type")))]
        [#t (triggered (exception "Bad Expression."))]
        ))

(define (greater e1 e2)
    (mul (?leq e2 e1) (~ (mul (?leq e2 e1) (?leq e1 e2)))))


(define revHelper (fun "rev" (list "list" "acc")
    (if-then-else (?empty (valof "list"))
        (valof "acc")
        (call (valof "rev") (list (tail (valof "list")) (.. (head (valof "list")) (valof "acc"))))
    )
))

(define (rev e) 
    (call revHelper (list e (empty))))  

(define mappingHelp (fun "mapping" (list "seq" "f")
    (if-then-else (?empty (valof "seq"))
        (empty)
        (.. (call (valof "f") (list (head (valof "seq"))))
            (call (valof "mapping") (list (tail (valof "seq")) (valof "f")))))))

(define (mapping f seq)
    (call mappingHelp (list seq f)))


(define filterHelp (fun "filtering" (list "seq" "f")
    (if-then-else (?empty (valof "seq"))
        (empty)
        (if-then-else (call (valof "f") (list (head (valof "seq"))))
            (.. (head (valof "seq")) (call (valof "filtering") (list (tail (valof "seq")) (valof "f"))))
            (call (valof "filtering") (list (tail (valof "seq")) (valof "f")))))))

(define (filtering f seq)
    (call filterHelp (list seq f)))  


(define foldingHelp (fun "folding" (list "f" "init" "seq")
    (if-then-else (?empty (valof "seq"))
        (valof "init")
        (if-then-else (?empty (tail (valof "seq")))
            (call (valof "f") (list (head (valof "seq")) (valof "init")))
            (call (valof "folding") (list (valof "f") 
                                       (call (valof "f") (list (valof "init") (head (valof "seq")))) 
                                       (tail (valof "seq"))))))))

(define (folding f init seq)
    (call foldingHelp (list f init seq)))

(define binaryHelper (fun "binary" (list "num" "pow2")
    (if-then-else (greater (valof "pow2") (valof "num"))
    (.. (valof "num") (empty))
    (vars "solution" (call (valof "binary") (list (valof "num") (mul (int 2) (valof "pow2"))))
        (if-then-else (?leq (int 0)  (add (~ (valof "pow2")) (head (valof "solution"))))
            (.. (add (~ (valof "pow2")) (head (valof "solution"))) (.. (int 1) (tail (valof "solution"))))
            (.. (head (valof "solution")) (.. (int 0) (tail (valof "solution")))))))))

(define (binary num)
    (if-then-else (?= (int 0) num)
        (.. (int 0) (empty))
        (rev (tail (call binaryHelper (list num (int 1)))))))