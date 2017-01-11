;; compiler test
;; Author: Ofir Etz-Hadar

(load "compiler.scm")

(define fails 0)
(define total 0)
(define show-test #f)    ; set this to #t if you like

(define (test input out-str)
  (set! total (+ total 1))
  (let ((format-out (parse input)))
    (if (equal? out-str format-out)
        (if show-test
            (begin
              (display "Verified ")
              (write input)
              (newline)))
        (begin
          (set! fails (+ fails 1))
          (if (not show-test) (newline))
          (display "Failed in test No. ")
          (write total)
          (display ": ")
          (write input)
          (display " returns ")
          (write format-out)
          (display " instead of ")
          (write out-str)
          (newline)))))

(define (g-test proc input out-str)
  (set! total (+ total 1))
  (let ((format-out (proc input)))
    (if (equal? out-str format-out)
        (if show-test
            (begin
              (display "Verified ")
              (write input)
              (newline)))
        (begin
          (set! fails (+ fails 1))
          (if (not show-test) (newline))
          (display "Failed in test No. ")
          (write total)
          (display ": ")
          (write input)
          (display " returns ")
          (write format-out)
          (display " instead of ")
          (write out-str)
          (newline)))))

;#1
; Parse constant test(1-8)

(test '2 '(const 2))
(test '2222 '(const 2222))
(test '#\a '(const #\a))
(test '#t '(const #t))
(test '#f '(const #f))
(test '"This is a string" '(const "This is a string"))
(test '(quote (quote a b c)) '(const (quote a b c)))
(test '(quote a) '(const a))

;#2
; Parse variable test(9-14)

(test 'a '(var a))
(test 'abc '(var abc))
(test '123x '(var 123x))
(test 'x123 '(var x123))
(test '1x2x3 '(var 1x2x3))

;#3
; Parse conditional test(15-18)

(test '(if a b c) '(if3 (var a) (var b) (var c)))
(test '(if a b) `(if3 (var a) (var b) (const ,(void))))
(test '(if (if a b c) (if d (if e f g)) h) `(if3 (if3 (var a) (var b) (var c)
  ) (if3 (var d) (if3 (var e) (var f) (var g)) (const ,(void))) (var h)))

;#4
; Parse lambda forms test

  ;#4.1 
  ; lambda-simple(19-25)

(test '(lambda (x y z) (if x y z)) '(lambda-simple (x y z) (if3 (var x) (var y) (var z))))
(test '(lambda () a) '(lambda-simple () (var a)))
(test '(lambda () (quote (quote a b c))) '(lambda-simple () (const (quote a b c))))
(test '(lambda () (if #t 1 2)) '(lambda-simple () (if3 (const #t) (const 1) (const 2))))
(test '(lambda (a b c) (if a b c) a b) '(lambda-simple (a b c) (seq ((if3 (var a) (var b) (var c)) (var a) (var b))))) ;without 'begin'
(test '(lambda (a b c) (begin (if a b c) a b)) '(lambda-simple (a b c) (seq ((if3 (var a) (var b) (var c)) (var a) (var b)))))


  ;#4.2 
  ; lambda-opt(26-30)

(test '(lambda (x y z . rest) (if x y z)) '(lambda-opt (x y z) rest (if3 (var x) (var y) (var z))))
(test '(lambda (x . rest) rest) '(lambda-opt (x) rest (var rest)))
(test '(lambda (x . rest) rest rest 1) '(lambda-opt (x) rest (seq ((var rest) (var rest) (const 1))))) ;without 'begin'
(test '(lambda (x . rest) (begin rest rest 1)) '(lambda-opt (x) rest (seq ((var rest) (var rest) (const 1))))) 

  ;#4.3 
  ; lambda-variadic(31-35)

(test '(lambda args (if x y z)) '(lambda-variadic args (if3 (var x) (var y) (var z))))
(test '(lambda args args) '(lambda-variadic args (var args)))
(test '(lambda args args x y z) '(lambda-variadic args (seq ((var args) (var x) (var y) (var z))))) ;without 'begin'
(test '(lambda args (begin args x y z)) '(lambda-variadic args (seq ((var args) (var x) (var y) (var z)))))

;#5
; Parse sequences test(34-37)

(test '(begin a b c) '(seq ((var a) (var b) (var c))))
(test '(begin a (if #t #t #f) c) '(seq ((var a) (if3 (const #t) (const #t) (const #f)) (var c))))
(test '(begin) `(const ,(void))) ; Took from the assignment's forum

;#6
; Parse define test

  ;#6.1
  ; Regular define(38-44)

(test '(define x 5) '(define (var x) (const 5)))
(test '(define x (lambda (x) x)) '(define (var x) (lambda-simple (x) (var x))))
(test '(define x (lambda (x) x 5)) '(define (var x) (lambda-simple (x) (seq ((var x) (const 5))))))
(test '(define x (lambda (x y . rest) rest)) '(define (var x) (lambda-opt (x y) rest (var rest))))
(test '(define f (lambda (x . rest) rest rest 1)) '(define (var f) (lambda-opt (x) rest (seq ((var rest) (var rest) (const 1)))))) ;without 'begin'
(test '(define f (lambda (x . rest) (begin rest rest 1))) '(define (var f) (lambda-opt (x) rest (seq ((var rest) (var rest) (const 1)))))) 

  ;#6.2
  ; MIT-style define(45-55)

(test '(define (id x) x x) '(define (var id) (lambda-simple (x) (seq ((var x) (var x))))))
(test '(define (id x) x) '(define (var id) (lambda-simple (x) (var x))))
(test '(define (foo x y z) (if x y z)) '(define (var foo) (lambda-simple (x y z) (if3 (var x) (var y) (var z)))))
(test '(define (foo x y . z) (if x y z)) '(define (var foo) (lambda-opt (x y) z (if3 (var x) (var y) (var z)))))
(test '(define (foo x y . z) (if x y z) x) '(define (var foo) (lambda-opt (x y) z (seq ((if3 (var x) (var y) (var z)) (var x))))))
(test '(define (list . args) args) '(define (var list) (lambda-variadic args (var args))))
(test '(define (list . args) (if #t #t #f)) '(define (var list) (lambda-variadic args (if3 (const #t) (const #t) (const #f)))))
(test '(define (list . args) args 1 args) '(define (var list) (lambda-variadic args (seq ((var args) (const 1) (var args)))))) ;without begin
(test '(define (list . args) (begin args 1 args)) '(define (var list) (lambda-variadic args (seq ((var args) (const 1) (var args))))))
(test '(define (fact n) (if (zero? n) 1 (* n (fact (- n 1))))) `(define (var fact) (lambda-simple (n) (if3 (applic (var zero?) ((var n))) (const 1) (applic (var *) ((var n) (applic (var fact) ((applic (var -) ((var n) (const 1)))))))))))

;#7
; Parse application test(56-59)

(test '(a) '(applic (var a) ()))
(test '(a b c) '(applic (var a) ((var b) (var c))))
(test '((a b) (a c)) '(applic (applic (var a) ((var b))) ((applic (var a) ((var c))))))

;#8
; Parse 'let' test(using Macro-Expansion) (60-64)

(test '(let ((a 1) (b 2)) a) `(applic (lambda-simple (a b) (var a)) ((const 1) (const 2))))
(test '(let ((a 1) (b 2)) a a) `(applic (lambda-simple (a b) (seq ((var a) (var a)))) ((const 1) (const 2))))
(test '(let () 1) `(applic (lambda-simple () (const 1)) ()))
(test '(let ((v1 e1) (v2 e2)) b1 b2 b3) `(applic (lambda-simple (v1 v2) (seq ((var b1) (var b2) (var b3)))) ((var e1) (var e2))))

;#9
; Parse 'let*'' test (65)

(test '(let* ((v1 e1) (v2 e2)) b1 b2 b3) `(applic (lambda-simple (v1) (applic (lambda-simple (v2) (seq ((var b1) (var b2) (var b3)))) ((var e2)))) ((var e1))))

;#10
; Parse 'letrec' test(using Macro-Expansion)

;(test '((letrec ((helper (lambda (x) x))) (helper 1))) `(applic (var Ym) ((lambda-simple (g0 helper) (applic (var helper) ((const 1)))) (lambda-simple (g0 helper) (lambda-simple (x) (var x))))))

;#11
; Parse 'and' test(using Macro-Expansion)

(test '(and) `(const #t))
(test '(and (and #t #t) #f) `(if3 (if3 (const #t) (const #t) (const #f)) (const #f) (const #f)))
(test '(and a b c d e f) `(if3 (var a) (if3 (var b) (if3 (var c) (if3 (var d) (if3 (var e) (var f) (const #f)) (const #f)) (const #f)) (const #f)) (const #f)))

;#12
; Parse 'cond' test(using Macro-Expansion)

(test '(cond (else 1)) `(const 1))
(test '(cond (#t #f)) `(if3 (const #t) (const #f) (const ,(void))))
(test '(cond ((zero? n) 1) ((positive? n) 2) (else 5)) `(if3 (applic (var zero?) ((var n))) (const 1) (if3 (applic (var positive?) ((var n))) (const 2) (const 5))))

;#13
; Parse 'quasiquote' test

(test '(quasiquote a ,b ,@c) `(const (cons 'a (cons b (append c '())))))
(test '(quasiquote a b c) `(const (cons 'a (cons 'b (cons 'c '())))))
(test '(quasiquote a ,b c) `(const (cons 'a (cons b (cons 'c '())))))
(test '(quasiquote ,@a ,b c) `(const (append a (cons b (cons 'c '())))))

;#14
; eval-constant test

(g-test eval-constant `(const #t) #t)
(g-test eval-constant `(const #\a) #\a)
(g-test eval-constant `(const 2) 2)

;#15
; eval-if test

(g-test eval-if `((const #t) (const 1) (const 2)) 1)
(g-test eval-if `((const #t) (const 1) (const ,(void))) 1)
(g-test eval-if `((const 2) (const 1) (const 2)) 1)
(g-test eval-if `((const #f) (const 1) (const 2)) 2)

;#16
; predicate-op? test

(g-test predicate-op? `(applic (var number?) ((const 1))) #t)
(g-test predicate-op? `(applic (var zero?) ((const 1))) #t)
(g-test predicate-op? `(applic (var null?) ((const 1))) #t)
(g-test predicate-op? `(applic (var string?) ((const 1))) #t)

;#17
; flatten-plus test

(g-test flatten-plus `(+ 1 (+ 2 x) (+ 2 y)) `(+ 1 2 x 2 y))
(g-test flatten-plus `(+ (+ 2 x) (+ 2 y)) `(+ 2 x 2 y))
(g-test flatten-plus `(+ (+ 2 x y) (+ 2 y)) `(+ 2 x y 2 y))
(g-test flatten-plus `(+ (+ 2 x z) (+ 2 z y)) `(+ 2 x z 2 z y))
(g-test flatten-plus `(+ 1 (+) 1) `(+ 1 (+) 1))
;(g-test flatten-plus `(+ 1 (+ 2 (+ 1 3)) 1) `(+ 1 2 1 3 1))
;(g-test flatten-plus `(+ 1 (+ 2 (+ 1 x)) 1) `(+ 1 2 1 x 1))

;#18
; symbols-sort test

(g-test symbols-sort `(a t t a a b c b z) `(a a a b b c t t z))

;#19
; mege-muls test

(g-test merge-muls `(+ 1 (* -1 x) (* 3 x) (* 2 x) (* 1 y)) `(+ 1 (* 4 x) (* 1 y)))
(g-test merge-muls `(+ 1 (* 3 y) (* 2 x) (* 1 y)) `(+ 1 (* 4 y) (* 2 x)))
(g-test merge-muls `(+ 1 2 (* 2 x)) `(+ 1 2 (* 2 x)))
(g-test merge-muls `(+ 1 2) `(+ 1 2))

;#20
; muls-union test

(g-test muls-union `((* 2 x) (* 3 x)) `(* 5 x))
(g-test muls-union `((* -1 x) (* 2 x) (* 3 x)) `(* 4 x))

;#21
; fold-plus test

(g-test fold-plus (parse `(+)) 0)
(g-test fold-plus (parse `(+ 1)) 1)
(g-test fold-plus (parse `(+ (+ 2 3))) 5)
(g-test fold-plus (parse `(+ 2 x)) `(+ 2 x))
(g-test fold-plus (parse `(+ (+ 2 x))) `(+ 2 x))
(g-test fold-plus (parse `(+ (+ 2 x) 4 (+ 3 y))) `(+ 9 x y))
;(g-test fold-plus (parse `(+ (+ 2 x z) 4 (+ 3 y))) `(+ 9 x z y))

;#22
; fold-mul test
;
; **Remember that we are not required to fold expressions where this would require the distributive laws**

(g-test fold-mul (parse `(*)) 1)
(g-test fold-mul (parse `(* 1)) 1)
(g-test fold-mul (parse `(* (* 2 3))) 6)
(g-test fold-mul (parse `(* 2 x)) `(* 2 x))
(g-test fold-mul (parse `(* 1 x)) `x)
(g-test fold-mul (parse `(* (* 2 x))) `(* 2 x))
(g-test fold-mul (parse `(* (* 2 x) 4 (* 3 y))) `(* 24 x y))
(g-test fold-mul (parse `(* (* 2 x z) 4 (* 3 y))) `(* 24 x z y))
(g-test fold-mul (parse `(* x 2)) `(* 2 x))
(g-test fold-mul (parse `(* (* 2 x) 4 (* y 3))) `(* 24 x y))

;#23
; flatten-mul test

(g-test flatten-mul `(* 1 (* 1 x) (* 2 y) (* 1 z) (* 5 t) (* 7 z)) `(* 1 1 x 2 y 1 z 5 t 7 z))
(g-test flatten-mul `(* 1 (* 1 x) (* 2 y) (* 2 x) (* 5 t) (* 7 z)) `(* 1 1 x 2 y 2 x 5 t 7 z))

;#24
; flatten-junk-mul test

(g-test flatten-junk-mul `(+ 1 (* 1 x)) `(+ 1 x))
(g-test flatten-junk-mul `(+ 1 (* 1 x) (* 2 x)) `(+ 1 x (* 2 x)))
(g-test flatten-junk-mul `(+ (* 1 x)) `(+ x))
(g-test flatten-junk-mul `(+ 1 (* 1 x) (* 1 y) 2) `(+ 1 x y 2))

;#25
; vars->mul test

(g-test vars->mul (parse `(+ 1 x (* 1 y) (* 2 z) w 2)) (parse `(+ 1 (* 1 x) (* 1 y) (* 2 z) (* 1 w) 2)))
(g-test vars->mul (parse `(* 1 x (* 1 y) (* 2 z) w 2)) (parse `(* 1 (* 1 x) (* 1 y) (* 2 z) (* 1 w) 2)))
(g-test vars->mul (parse `(* x y)) (parse `(* (* 1 x) (* 1 y))))
;(g-test vars->mul (parse `(* x y)) (parse `(* (* 1 x) (* 1 y))))

;#26
; multiplication-of-one test

(g-test multiplication-of-one? (parse `(* 1 x)) #t)
(g-test multiplication-of-one? (parse `(* 1 x y)) #f)
(g-test multiplication-of-one? (parse `(+ 1 (* 1 x) y)) #f)
(g-test multiplication-of-one? (parse `(1)) #f)

;#27
; add1-arg test

(g-test add1-arg (parse `(add1 1)) `(const 1))
(g-test add1-arg (parse `(add1 x)) `(var x))

;#28
; add1-op?

(g-test add1-op? (parse `(add1 x)) #t)
(g-test add1-op? (parse `(add1 1)) #t)
(g-test add1-op? (parse `(+ 2 x)) #f)

;#
; Fold procedure test

(g-test fold '(+ 4 5 -4 -5 0) 0)
(g-test fold '(+ 0 3 -4 x) '(+ -1 x))
(g-test fold '(+ (+ 2 3) (+ 5 x y)) `(+ 10 x y))
(g-test fold '(* 4 5 -4 -5) 400)
(g-test fold '(* 3 -4 x) '(* -12 x))
(g-test fold '(* (+ 2 3) (* 5 x y)) `(* 25 x y))
(g-test fold '(+ 4 5 -4 -5 0 (*) (+)) 1)
(g-test fold '(+ 4 5 -4 -5 0 (*))  1)
(g-test fold '(+ 4 5 -4 -5 0 (+)) 0)
(g-test fold '(+) 0)
(g-test fold '(*) 1)
(g-test fold '(* 5) 5)
(g-test fold '(+ 4) 4)
(g-test fold '(+ (+ 3 (* 4 (+)))) 3)
(g-test fold '(* (* 3 (+ 4 (*)))) 15)
(g-test fold `(add1 1) 2)
(g-test fold `(sub1 1) 0)
;(g-test fold '(cdr (cons x 'a)) 'a)
;(g-test fold '(car (car x)) `(caar x))
;(g-test fold '(car (cdr x)) `(cadr x))
;(g-test fold '(cdr (car x)) `(cdar x))
;(g-test fold '(cdr (cdr x)) `(cddr x))
;(g-test fold '(null? '()) #t)
;(g-test fold '(null? '(a b c)) #t)
;(g-test fold '(null? (cons a b)) #f)
;(g-test fold '(null? (list)) #t)
;(g-test fold '(if (zero? 5) 'not-ok 'ok) 'ok)
;(g-test fold '(null? (if x '() '())) #t)
;(g-test fold '(+ (+ (car '(1 2 3)) (cdr (cons v 6))) (* 3 4 y) (add1 (+ 3 4 x))) `(+ 15 x (* 12 y)))
;(g-test fold '(+ x x) `(* 2 x))
;(g-test fold '(+ 2 y x z x) `(+ 2 y z (* 2 x)))
;(g-test fold '(append '() '(a b c)) `(a b c))
;(g-test fold '(append '(a b c) '()) `(a b c))
;(g-test fold '(append '(a b c) '(d e f) '(g h)) `(a b c d e f g h))
;(g-test fold '(string-append "" "def") "def")
;(g-test fold '(string-append "abc" "") "abc")
;(g-test fold '(string-append "abc" "def") "abcdef")
;(g-test fold `(cons 1 2) `(1 2))
(g-test fold `(list 1 2 x 4) `(1 2 x 4))
;(g-test fold `(number? 1) #t)
;(g-test fold `(number? `x) #f)
;(g-test fold `(zero? 0) #t)
;(g-test fold `(string? "x") #t)


(format #t "~%~a Test~:p completed. (~a failure~:p)~2%" total fails)