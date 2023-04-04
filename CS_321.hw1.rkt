#lang plai
(define eight-principles
  (list "Know your rights."
        "Acknowledge your sources."
        "Protect your work."
        "Avoid suspicion."
        "Do your own work."
        "Never falsify a record or permit another person to do so."
        "Never fabricate data, citations, or experimental results."
        "Always tell the truth when discussing your work with your instructor."))

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?))
          (body FnWAE?)])

;can change the interface so that now fnwae can take a list

(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [with (id symbol?)
        (expr FnWAE?)
        (body FnWAE?)]
  [id (name symbol?)]
  ;app needs to change, function definitions also need to change
  [app (fun-name symbol?)
       (arg (listof FnWAE?))])

(define (check-pieces expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))

(define (check-piece expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))

(define (parse-error what expression)
  (error 'parser
         "expected: ~a, found: ~a"
         what
         expression))

(define (parse s-exp)
  (cond [(number? s-exp) (num s-exp)]
        [(symbol? s-exp) (id s-exp)]
        [(list? s-exp)
         (when (empty? s-exp)
           (error 'parse "the empty list is not a valid FnWAE"))
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got: ~a" (first (second s-exp))))
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [else
            (check-piece (list (first s-exp)) 1 "function application")
            (unless (symbol? (first s-exp))
              (error 'parse "expected a function name, got: ~a" (first s-exp)))
            (app (first s-exp)
                 (map parse (rest s-exp)))])]
        [else
         (error 'parse "expected an F1WAE, got: ~a" s-exp)]))

;if you start with interp, then it might be easier to think about how to change the define-type

(test (parse '{+ 1 2}) (add (num 1) (num 2)))

(test (parse 1) (num 1))

(test (parse 'z) (id 'z))

(test (parse `{f 10})
      (app 'f (list (num 10))))

(test (parse '{f a b c})
      (app 'f (list (id 'a)
                    (id 'b)
                    (id 'c))))

(test (parse '{f 1 2})
      (app 'f (list (num 1) (num 2))))

(define (parse-defn def-expr)
  (case (first def-expr)
    [(deffun)
       (check-pieces def-expr 3 "deffun")
       
       (define (illdef? def-expr bool-lst)
         (if (empty? def-expr) false
             (if (member (first def-expr) bool-lst)
                 true
                 (illdef? (rest def-expr) (append (list (first def-expr)) bool-lst)))))
       
       (cond
         [(illdef? (rest (second def-expr)) '()) (error "bad syntax" def-expr)]
         [else (fundef (first (second def-expr))
                       (rest (second def-expr))
                       (parse (third def-expr)))])]
    [else (parse-error "deffun" def-expr)]))

(test (parse-defn '{deffun {f x y} {+ x y}})
      (fundef 'f '(x y) (add (id 'x) (id 'y))))

(test (parse-defn '{deffun {f} 5})
      (fundef 'f '() (num 5)))

;Now time for interp
(define (interp an-fnwae fundefs)
  (type-case FnWAE an-fnwae
    [num (n) n]
    [add (lhs rhs)
         (+ (interp lhs fundefs)
            (interp rhs fundefs))]
    [sub (lhs rhs)
         (- (interp lhs fundefs)
            (interp rhs fundefs))]
    [with (name named-expr body)
          (interp (subst body
                         name
                         (interp named-expr fundefs))
                  fundefs)]
    [id (name)
        (error 'interp "free identifier: ~a" name)]
    [app (fun-name arg)
         (local [(define a-fundef
                   (lookup-fundef fun-name fundefs))]
         ;(error "testing error" a-fundef)
           
         (define (my-subst body param-name arg)
           (if (and (not (empty? arg)) (empty? param-name)) (error "wrong arity")
               (if (and (empty? arg) (not (empty? param-name))) (error "wrong arity")
                   (if (equal? '() param-name)
                       body
                       (my-subst
                        (subst body
                               (first param-name)
                               (interp (first arg) fundefs))
                        (rest param-name)
                        (rest arg))))))

         (type-case FunDef a-fundef
           [fundef (fun-name param-name body)
                   ;arg will have (list id's)
                   ;need to check that this equals number of variables in
                   ;length of param-name does not matter
                       (interp (my-subst body
                                         param-name
                                         arg)
                               fundefs)]))]))

(define (lookup-fundef name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" name)]
        [(equal? name (fundef-fun-name (first fundefs)))
         ;(error "first fundefs are" (first fundefs))]
         (first fundefs)]
        [else
         (lookup-fundef name (rest fundefs))]))

;; subst : FnWAE? symbol? number? -> FnWAE?
(define (subst a-fnwae name value)
  (type-case FnWAE a-fnwae
    [num (n)
         a-fnwae]
    [add (l r)
         (add (subst l name value)
              (subst r name value))]
    [sub (l r)
         (sub (subst l name value)
              (subst r name value))]
    [with (name2 named-expr body)
          (with name2 (subst named-expr name value)
                (if (equal? name name2)
                    body
                    (subst body name value)))]
    [id (name2)
        (if (equal? name name2)
            (num value)
            a-fnwae)]
    [app (fun-name arg)
         (define (subst-map my-arg-expr)
           (subst my-arg-expr name value))
         (app fun-name (map subst-map arg))]))

(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)

(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)

(test/exn (interp (parse '{with {x y} 1})
                  (list))
          "free identifier")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x x} {+ x x}})))
          "bad syntax")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {g a b c} c})))
          "undefined function")

(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")

(test/exn (interp (parse '{f x})
                  (list (parse-defn '{deffun {f a b c} c})))
          "free identifier")

(test/exn (interp (parse '(f 1 2 3))
                  (list (parse-defn '(deffun (f x y) (+ x y)))))
          "wrong arity")

(test/exn (interp (parse '(f 1 2 3 4 5))
                  (list (parse-defn '(deffun (f x y) (+ x y)))))
          "wrong arity")

(test/exn (interp (parse '(f 8 2 7 11))
                  (list (parse-defn '(deffun (f x y z) (+ x y)))))
          "wrong arity")