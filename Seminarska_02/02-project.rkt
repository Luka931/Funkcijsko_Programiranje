#lang racket

(require compatibility/mlist)

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

; HelperFunctions for fri interpreter

(define (isBool? e)
    (or (true? e) (false? e)))

(define (isSeq? seq) 
    (if (..? seq) 
        (let*
        ([e2 (..-e2 seq)])
        (if (..? e2)
            (isSeq? e2)
            (empty? e2)))
        #f))

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
    (if (<= (int-int e1) (int-int e2))
        (true)
        (false)))

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

(define (isInList? el seq)(let*
    ([hd (car seq)]
     [tl (cdr seq)])
    (if (and (equal? tl null) (not (equal? hd el)))
        #f
    (if (equal? hd el)
        #t
        (isInList? el tl)))))

(define (allUnique seq)
    (if (or (null? seq) (= (length seq) 1))
        #t
    (let ([hd (car seq)]
          [tl (cdr seq)])
    (if (isInList? hd tl)
        #f
    (allUnique tl)))))

(define (copyEnv env)
    (if (null? env)
        null
        (mappend (mlist (mcons (mcar (mcar env)) (mcdr (mcar env)))) (copyEnv (mcdr env)))
    )
)

(define (expandEnvOne env s e1)(letrec
    ([newEnv (copyEnv env)]
     [exsisting (massoc s newEnv)]
     [evaluated (if (closure? e1) e1 (friWithEnv env e1))])
    (if (triggered? evaluated)
        evaluated
    (if exsisting
        (begin 
            (set-mcdr! exsisting evaluated)
            newEnv)
        (mappend newEnv (mlist (mcons s evaluated)))))
))

; (define (expandEnvOne env s e1) (letrec
;     ([envCopy (hash-copy env)]
;      [evaluated (if (closure? e1) e1 (friWithEnv env e1))]) 
;     (if (triggered? evaluated)
;         evaluated
;         (begin
;             (hash-set! envCopy s evaluated)
;             envCopy
;         ))))

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

(define (fri e)
    (friWithEnv null e))
        
(define (friWithEnv env e)
    (cond
        [(int? e) e]
        [(true? e) e]
        [(false? e) e]
        [(..? e) (letrec
            ([e1 (friWithEnv env (..-e1 e))]
             [e2 (friWithEnv env (..-e2 e))])
            (.. e1 e2))]
        [(empty? e) e]
        [(exception? e) e]
        [(trigger? e) (letrec
            ([evaluated (friWithEnv env (trigger-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (exception? evaluated)
                (triggered evaluated)
                (triggered (exception "trigger: wrong argument type")))))]
        [(handle? e)(letrec
            ([e1 (friWithEnv env (handle-e1 e))]
             [e2 (friWithEnv env (handle-e2 e))]
             [e3 (handle-e3 e)])
            (if (not (triggered? e1))
                (triggered (exception "trigger: wrong argument type"))
            (if (equal? e1 e2)
                (friWithEnv env e3)
                e2)))]
        [(if-then-else? e) (letrec
            ([condition (friWithEnv env (if-then-else-condition e))]
             [e1 (if-then-else-e1 e)]
             [e2 (if-then-else-e2 e)])
            (if (triggered? condition)
                condition
            (if (false? condition)
                (friWithEnv env e2)
                (friWithEnv env e1))))]
        [(?int? e) (letrec
            ([evaluated (friWithEnv env (?int-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (int? evaluated)
                (true)
                (false))))]
        [(?bool? e) (letrec
            ([evaluated (friWithEnv env (?bool-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (isBool? evaluated)
                (true)
                (false))))]
        [(?..? e) (letrec
            ([evaluated (friWithEnv env (?..-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (..? evaluated)
                (true)
                (false))))]
        [(?empty? e)(letrec
            ([evaluated (friWithEnv env (?empty-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (empty? evaluated)
                (true)
                (false))))]
        [(?seq? e)(letrec
            ([evaluated (friWithEnv env (?seq-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (isSeq? evaluated)
                (true)
                (false))))]
        [(?exception? e)(letrec
            ([evaluated (friWithEnv env (?exception-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (exception? evaluated)
                (true)
                (false))))]
        [(add? e)(letrec
            ([e1 (friWithEnv env (add-e1 e))]
             [e2 (friWithEnv env (add-e2 e))])
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
            ([e1 (friWithEnv env (mul-e1 e))]
             [e2 (friWithEnv env (mul-e2 e))])
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
            ([e1 (friWithEnv env (?leq-e1 e))]
             [e2 (friWithEnv env (?leq-e2 e))])
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
            ([e1 (friWithEnv env (?=-e1 e))]
             [e2 (friWithEnv env (?=-e2 e))])
            (if (triggered? e1)
                e1
            (if (triggered? e2)
                e2
            (if (equal? e1 e2)
                (true)
                (false)))))]
        [(head? e)(letrec
            ([evaluated (friWithEnv env (head-e e))])
            (if (..? evaluated)
                (..-e1 evaluated)
            (if (empty? evaluated)
                (triggered (exception "head: empty sequence"))
                (triggered (exception "head: wrong argument type")))))]
        [(tail? e)(letrec
            ([evaluated (friWithEnv env (tail-e e))])
            (if (..? evaluated)
                (..-e2 evaluated)
            (if (empty? evaluated)
                (triggered (exception "tail: empty sequence"))
                (triggered (exception "tail: wrong argument type")))))]
        [(~? e)(letrec
            ([evaluated (friWithEnv env (~-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (isBool? evaluated)
                (bool~ evaluated)
            (if (int? evaluated)
                (int~ evaluated)
                (triggered (exception "~: wrong argument type"))))))]
        [(?all? e)(letrec
            ([evaluated (friWithEnv env (?all-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (isSeq? evaluated)
                (if (not (seqContainsFalse? evaluated))
                    (true)
                    (false))
                (triggered (exception "?all: wrong argument type")))))]
        [(?any? e)(letrec
            ([evaluated (friWithEnv env (?any-e e))])
            (if (triggered? evaluated)
                evaluated
            (if (isSeq? evaluated)
                (if (not (seqContainsAllFalse? evaluated))
                    (true)
                    (false))
                (triggered (exception "?any: wrong argument type")))))]
        [(vars? e)(letrec
            ([s (vars-s e)]
             [e1 (vars-e1 e)]
             [e2 (vars-e2 e)]
             [newEnv (expandEnvironment env s e1 )])
            (if (triggered? newEnv)
                  newEnv
                  (friWithEnv newEnv e2)))]
        [(valof? e)(let
            ([value (massoc (valof-s e) env)])
            (if value
                (mcdr value)
                (triggered (exception "valof: undefined variable"))))]
            ; (hash-ref env (valof-s e) (lambda () (triggered (exception "valof: undefined variable"))))
        [(fun? e)(letrec
            ([farg (fun-farg e)])
            (if (allUnique farg)
                (closure env e)
                (triggered (exception "fun: duplicate argument identifier"))))]
        [(proc? e) e]
        [(call? e)(letrec
            ([args (map (lambda (e) (friWithEnv env e)) (call-args e))]
             [clOrProc (friWithEnv env (call-e e))])
            (if (triggered? clOrProc)
                clOrProc
            (if (closure? clOrProc)(letrec
                ([envFun (closure-env clOrProc)]
                 [farg (fun-farg (closure-f clOrProc))]
                 [body (fun-body (closure-f clOrProc))]
                 [name (fun-name (closure-f clOrProc))])
                (if (= (length args) (length farg))
                    (friWithEnv (expandEnvironment (expandEnvironment envFun name clOrProc) farg args) body)
                    (triggered (exception "call: arity mismatch"))))
            (if (proc? clOrProc)(letrec
                ([name (proc-name clOrProc)]
                 [body (proc-body clOrProc)])
                (begin
                    [expandEnvironment env name clOrProc]
                    [friWithEnv env body]))
                (triggered (exception "call: wrong argument type"))))
            )
        )]
        

        [#t (triggered (exception "Bad Expression."))]
        ))

(define (greater e1 e2)
    (mul (?leq e2 e1) (~ (and (?leq e2 e1) (?leq e1 e2)))))


(define revHelper (fun "rev" (list "list" "acc")
    (if-then-else (?empty (valof "list"))
        (valof "acc")
        (call (valof "rev") (list (tail (valof "list")) (.. (head (valof "list")) (valof "acc"))))
    )
))

(define (rev e) 
    (call revHelper (list e (empty))))  

(define mappingHelp (fun "map" (list "seq" "f")
    (if-then-else (?empty (tail (valof "seq")))
        (.. (call (valof "f") (list (head (valof "seq")))) (empty))
        (.. (call (valof "f") (list (head (valof "seq"))))
            (call (valof "map") (list (tail (valof "seq")) (valof "f")))))))

(define (mapping f seq)
    (call mappingHelp (list seq f)))


(define filterHelp (fun "filter" (list "seq" "f")
    (if-then-else (?empty (tail (valof "seq")))
        (if-then-else (call (valof "f") (list (head (valof "seq"))))
            (.. (head (valof "seq")) (empty))
            (empty))
        (if-then-else (call (valof "f") (list (head (valof "seq"))))
            (.. (head (valof "seq")) (call (valof "filter") (list (tail (valof "seq")) (valof "f"))))
            (call (valof "filter") (list (tail (valof "seq")) (valof "f")))))))

(define (filtering f seq)
    (call filterHelp (list seq f)))  


(define foldingHelp (fun "fold" (list "f" "init" "seq")
    (if-then-else (?empty (valof "seq"))
        (valof "init")
        (if-then-else (?empty (tail (valof "seq")))
            (call (valof "f") (list (valof "init") (head (valof "seq"))))
            (call (valof "fold") (list (valof "f") 
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
            (.. (head (valof "solution")) (.. (int 0) (tail (valof "solution"))))
        )
    ))
))

(define (binary num)
    (if-then-else (?= (int 0) num)
        (.. (int 0) (empty))
        (rev (tail (call binaryHelper (list num (int 1)))))
))


(fri (binary (int 15556)))

