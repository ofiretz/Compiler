;;; compiler.scm
;;; The compiler package
;;;
;;; Author: Ofir Etz-Hadar , 2015

(load "pattern-matcher.scm")
(print-graph #f) ; display circular structures
(print-gensym #f) ; print gensym as g1234
(case-sensitive #f) ; ditto
(print-brackets #f) ; do not use brackets when pretty-printing

(revert-interaction-semantics) ; allow builtins to be redefined

;;; fix bug in optimizer
(#%$sputprop 'append '*flags* 122)
(#%$sputprop 'append! '*flags* 34)
(#%$sputprop 'list* '*flags* 1250)
(#%$sputprop 'cons* '*flags* 1250)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART 2: The parser 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;; Parser: Miscellaneous ;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Generating #void

(define *void-object* (if #f #t))

; List of reserved words

(define *reserved-words*
  '(and begin cond define do else if lambda
    let let* letrec or quasiquote unquote 
    unquote-splicing quote set!))

; (apply arg2 arg1)

(define with 
	(lambda (arg1 arg2) (apply arg2 arg1)))

; (sequence->begin)

(define beginify
  (lambda (a)
    (cond ((null? a) *void-object*)
	  ((null? (cdr a)) (car a))
	  (else `(begin ,@a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;; Parser: Predicates ;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This procedure checks if some symbol is a reserved word

(define reserved?
  (lambda (a)
    (ormap (lambda (b) (eq? a b))
     *reserved-words*)))

; This procedure checks if some symbol is not a reserved word

(define !reserved?
	(lambda(a)
		(not (reserved? a))))

; Simple constant predicate

(define simple-const? 
	(lambda(a) (or (number? a) (char? a) (string? a) (boolean? a))))

; Variable predicate

(define var? (lambda(a) (and (symbol? a) (!reserved? a))))

; Checks if arg is a member of the list lst

(define member?
  (lambda (arg lst)
    (ormap
     (lambda (w) (eq? arg w))
     lst)))

; Checks if there is duplicate variable names in a let expression

(define dup-var-names?
	(lambda (vars)
		(cond ((null? vars) #f)
				((member? (car vars) (cdr vars)) #t)
				(else (dup-var-names? (cdr vars))))))

; Checks if there is no duplicate variable names in a let expression

(define !dup-var-names?
	(lambda (vars)
		(not (dup-var-names? vars))))

	 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;; Parser: Expanders ;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lambda Macro-Expander

(define lambda-syntax
	(lambda (a pro imp sym)
		(cond ((pair? a) 
				(lambda-syntax (cdr a)
					pro
					(lambda (s b) (imp (cons (car a) s) b))
					(lambda () (imp (list (car a)) (cdr a)))))
				((null? a) (pro))
				((symbol? a) (sym))
				(else (error 'lambdaExpander "Trying to expand this lambda expression")))))

; Let Macro-Expander

(define let-syntax
	(lambda (bidings body)
		(if (!dup-var-names? (map car bidings))
			`((lambda ,(map car bidings) ,(beginify body)) ,@(map cadr bidings)) ; Then
			(error 'letExpander "Duplicate variable names")) ; Else
		))

; I don't remember why this procedure is here, but ... 

(define expand-let
 (lambda (sexpr)
   (let ((args (map car (cadr sexpr)))
         (vals (map cadr (cadr sexpr)))
         (body (cddr sexpr)))
     (cond ((and (null? args) (null? vals)) `((lambda ,args ,@body) ))
           ((and (not (null? args)) (not (null? vals))) `((lambda ,args ,@body) ,@vals ))
           (else "error")))))


; Letrec expander

(define Yn
  (lambda fs
    (let ((ms (map
		  (lambda (fi)
		    (lambda ms
		      (apply fi
			     (map (lambda (mi)
				    (lambda args
				      (apply (apply mi ms) args)))
			       ms))))
		fs)))
      (apply (car ms) ms))))

(define letrec-syntax
  (lambda (e)
    (with e
      (lambda (_letrec ribs . exprs)
	(let* ((names `(,(gensym) ,@(map car ribs)))
	       (fs `((lambda ,names ,@exprs)
		     ,@(map (lambda (rib) `(lambda ,names ,(cadr rib)))
			 ribs))))
	  `(Yn ,@fs))))))

; And Macro-Expander(for 'and' with more then one expressions in its body)

(define and-syntax
	(lambda (exp rest)
		`(if ,exp (and ,@rest) #f)))

; Cond Macro-Expander(for 'cond' with more then one clause)

(define cond-syntax
	(lambda (exp exps)
		`(if ,(car exp) ,(beginify (cdr exp)) (cond ,@exps))))

; Quasiquote Macro-Expander
	  
(define expand-qq
  (lambda (e)
    (cond ((unquote? e) (cadr e))
	  ((unquote-splicing? e) (error 'expand-qq "unquote-splicing here makes no sense!"))
	  ((pair? e)
	   (let ((a (car e))
		 (b (cdr e)))
	     (cond ((unquote-splicing? a) `(append ,(cadr a) ,(expand-qq b)))
		   ((unquote-splicing? b) `(cons ,(expand-qq a) ,(cadr b)))
		   (else `(cons ,(expand-qq a) ,(expand-qq b))))))
	  ((vector? e) `(list->vector ,(expand-qq (vector->list e))))
	  ((or (null? e) (symbol? e)) `',e)
	  (else e))))

(define ^quote?
  (lambda (tag)
    (lambda (e)
      (and (pair? e)
	   (eq? (car e) tag)
	   (pair? (cdr e))
	   (null? (cddr e))))))

(define unquote? (^quote? 'unquote))
(define unquote-splicing? (^quote? 'unquote-splicing))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;; The Parser ;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse procedure

(define parse
  (let ((run
	 (compose-patterns
	  (pattern-rule
	   (? 'c simple-const?)
	   (lambda (c) `(const ,c)))
	  (pattern-rule
	   `(quote ,(? 'c))
	   (lambda (c) `(const ,c)))
	  (pattern-rule
	   (? 'v var?)
	   (lambda (v) `(var ,v)))
	  (pattern-rule
	   `(if ,(? 'test) ,(? 'dit))
	   (lambda (test dit)
	     `(if3 ,(parse test) ,(parse dit) (const ,*void-object*))))
	  (pattern-rule
	   `(if ,(? 'test) ,(? 'dit) ,(? 'dif))
	   (lambda (test dit dif)
	     `(if3 ,(parse test) ,(parse dit) ,(parse dif))))
	  ;; let
	  (pattern-rule
	   `(let ,(? 'bidings list?) . ,(? 'body))
	   (lambda (bidings body)
	     (parse (let-syntax bidings body))))
	  ;; let*
	  (pattern-rule
	   `(let* () ,(? 'expr) . ,(? 'exprs list?))
	   (lambda (expr exprs)
	     (parse (beginify (cons expr exprs)))))

	  (pattern-rule
	   `(let* ((,(? 'var var?) ,(? 'val)) . ,(? 'rest)) . ,(? 'exprs))
	   (lambda (var val rest exprs)
	     (parse `(let ((,var ,val))
		       (let* ,rest . ,exprs)))))
	  ;; letrec
	  (pattern-rule
	   `(letrec . ,(? 'c))
	   (lambda (c) (parse (letrec-syntax `(letrec . ,c)))))

	  ;; lambda
	  (pattern-rule
	   `(lambda ,(? 'args) ,(? 'expr))
	   (lambda (args expr)
			(lambda-syntax 
				args
				(lambda () `(lambda-simple ,args ,(parse expr)))
				(lambda (s a) `(lambda-opt ,s ,a ,(parse expr)))
				(lambda () `(lambda-variadic ,args ,(parse expr)))
				)))
	  ;; lambda2
	  	  (pattern-rule
	   `(lambda ,(? 'args) ,(? 'expr) . ,(? 'exprs list?))
	   (lambda (args expr exprs)
			(lambda-syntax 
				args
				(lambda () `(lambda-simple ,args ,(parse (beginify (cons expr exprs)))))
				(lambda (s a) `(lambda-opt ,s ,a ,(parse (beginify (cons expr exprs)))))
				(lambda () `(lambda-variadic ,args ,(parse (beginify (cons expr exprs)))))
				)))
	  ;; seq(begin) - no args
	  (pattern-rule
	   `(begin)
	   (lambda () `(const ,*void-object*)))	
	  ;; seq
	  (pattern-rule
	   `(begin . ,(? 'exprs list?))
	   (lambda (exprs) `(seq ,(map parse exprs))))	
	  ;; OR (empty)
	  (pattern-rule
	   `(or)
	   (lambda () (parse '#f)))
	  ;; OR (1 arg)
	  (pattern-rule
	   `(or ,(? 'expr))
	   (lambda (expr) `,(parse expr)))	
	  ;; OR (2+ arg)
	  (pattern-rule
	   `(or ,(? 'expr) .  ,(? 'exprs))
	   (lambda (expr exprs) `(or ,(map parse (cons expr exprs)))))
	  ;; MIT-style define - no multiple number of expressions in the body
	  (pattern-rule
	   `(define (,(? 'v var?) . ,(? 'vars)) ,(? 'exprs))
	   (lambda (v vars exprs) `(define ,(parse v) ,(parse (list 'lambda vars exprs)))))
	  ;; MIT-style define - multiple number of expressions in the body
	  (pattern-rule
	   `(define (,(? 'v var?) . ,(? 'vars)) ,(? 'exprs) . ,(? 'exprss)) 
	   (lambda (v vars exprs exprss) `(define ,(parse v) ,(parse (list 'lambda vars (beginify (cons exprs exprss)))))))
	  ;; regular define
	  (pattern-rule
	   `(define ,(? 'v var?) ,(? 'expr))
	   (lambda (v expr) `(define ,(parse v) ,(parse expr))))
	  ;; and - no expressions[(and) ==> #t]
	  (pattern-rule
	   `(and)
	   (lambda () (parse `#t)))
	  ;; and - exactly one expression
	  (pattern-rule
	   `(and ,(? 'exp))
	   (lambda (exp) `,(parse exp)))	
	  ;; and - multiple number of expressions(greater then one)
	  (pattern-rule
	   `(and ,(? 'exp) .  ,(? 'rest))
	   (lambda (exp rest) (parse (and-syntax exp rest))))
	  ;; cond - just 'else' clause
	  (pattern-rule
	   `(cond (else . ,(? 'exps list?)))
	   (lambda (exps) (parse `,(beginify exps))))	
	  ;; cond - with exactly one clause
	  (pattern-rule
	   `(cond ,(? 'exp list?))
	   (lambda (exp) (parse `(if ,(car exp) ,(beginify (cdr exp)))))) 
	  ;; cond - with multiple number of clauses(greater then one)
	  (pattern-rule
	   `(cond ,(? 'exp list?) .  ,(? 'exps))
	   (lambda (exp exps) (parse (cond-syntax exp exps))))	
	  ;; quasiquote
	  (pattern-rule
	   `(quasiquote . ,(? 'c))
	   (lambda (c) `(const ,(expand-qq c))))

      ;; application - no args
	  (pattern-rule
	   `(,(? 'v !reserved?))
	   (lambda (v) `(applic ,(parse v) ())))
	  ;; application 
	  (pattern-rule
	   `(,(? 'v !reserved?) . ,(? 'args))
	   (lambda (v args) `(applic ,(parse v) ,(map parse args))))


	  )))
    (lambda (e)
      (run e
	   (lambda ()
	     (error 'parse
		    (format "I can't recognize this: ~s" e)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PART 3: Fold
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;; Fold: Selectors ;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-constants-mul
	(lambda(e)
		(filter (lambda(a) (number? a)) e)
		))

(define get-non-constants-mul
	(lambda(e)
		(filter (lambda(a) (not (number? a))) e)
		))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;; Fold: Predicates ;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ifoldable
	(lambda(e)			
		(or (application-list? e) (symbol? e))
	))

; Symbol `() equality

(define constant-symbol-null?
	(lambda(e)
		(and (eq? 'const (car e)) (equal? (car `(`())) (cadr e)))))

; Symbol `() equality [I don't know if we realy need this... can be ignored]

(define symbol-null?
	(lambda(e)
		(equal? (car '('())) e)))

; Not a symbol predicate

(define !symbol?
	(lambda(e)
		(not (symbol? e))))

; Not a list predicate

(define !list?
	(lambda(e)
		(not (list? e))))


; Not a number predicate

(define !number?
	(lambda (e)
		(not (number? e))))

; Return #t iff exp contain epxression of the form (* <num>* <var>*)
; Examples: (contain-muls `(+ 1 2 (* 2 x))) ==> #t
; 			(contain-muls `(+ 1 2 x)) ==> #f

(define contain-muls
	(lambda(exp)
		(let ((muls (filter (lambda(e) (and (list? e) (< 1 (length e)) (eq? '* (car e)))) exp)))
			(if (null? muls) #f #t)
			)
		))

; muls list equals
; Examples: (muls-equal? `((* 2 x) (* 3 x))) ==> #t
;			(muls-equal? `((* 2 x) (* 3 y))) ==> #f
;			(muls-equal? `((* 2 x y z) (* 3 x y z))) ==> #f (this is because we want to union only muls-expr of length 3)

(define muls-equal?
	(lambda(m1 m2) 
		(and (= (length m1) 3) (= (length m2) 3) (equal? (cddr m1) (cddr m2)))
	))

(define !muls-equal?
	(lambda(m1 m2)
		(not (muls-equal? m1 m2))
	))

; Return #t iff e is not a variable and is not a 'cxr' OR 'append' expressions

(define appendable?
	(lambda(e)
		(if (and (not (symbol? e)) (if (and (list? e) (< 0 (length e)) (or (eq? 'append (car e)) (cxr-application? e))) #f #t)) #t #f)
		))

; Return #t iff e is not a variable and is not a 'cxr' OR 'string-append' expressions

(define string-appendable?
	(lambda(e)
		(if (and (not (symbol? e)) (if (and (list? e) (< 0 (length e)) (or (eq? 'string-append (car e)) (cxr-application? e))) #f #t)) #t #f)
		))

(define application-list?
	(lambda(exp)
		
		(if (and (list? exp) (> (length exp) 0) (or (eq? '+ (car exp)) 
			(eq? '* (car exp)) 
			(eq? 'list (car exp)) 
			(eq? 'cons (car exp)) 
			(eq? 'append (car exp))
			(eq? 'string-append (car exp))
			(eq? 'car (car exp))
			(eq? 'cdr (car exp))
			(eq? 'null? (car exp))
			(eq? 'number? (car exp))
			(eq? 'string? (car exp))
			(eq? 'zero? (car exp))
			(eq? 'if (car exp))
			;(eq? 'qoute (car exp))
			(eq? 'caar (car exp))
			(eq? 'caar (car exp))
			(eq? 'cadr (car exp))
			(eq? 'cdar (car exp))
			(eq? 'cddr (car exp))
			(eq? 'caaar (car exp))
			(eq? 'caadr (car exp))
			(eq? 'cadar (car exp))
			(eq? 'cdaar (car exp))
			(eq? 'cddar (car exp))
			(eq? 'cdadr (car exp))
			(eq? 'cdddr (car exp))
			(eq? 'caddr (car exp))
			(eq? 'caaaar (car exp))
			(eq? 'caaadr (car exp))
			(eq? 'caadar (car exp))
			(eq? 'cadaar (car exp))
			(eq? 'cdaaar (car exp))
			(eq? 'cddaar (car exp))
			(eq? 'cdadar (car exp))
			(eq? 'cdaadr (car exp))
			(eq? 'caddar (car exp))
			(eq? 'cadadr (car exp))
			(eq? 'caaddr (car exp))
			(eq? 'cdddar (car exp))
			(eq? 'cddadr (car exp))
			(eq? 'cdaddr (car exp))
			(eq? 'cadddr (car exp))
			);end-of-or
			);end-of-and
			#t #f);end-of-if
		))

; Return #t iff it's a list of some cXr expression

(define cxr-application?
	(lambda(exp)

		(if (and (list? exp) (> (length exp) 0) (or 
			(eq? 'car (car exp))
			(eq? 'cdr (car exp))
			(eq? 'caar (car exp))
			(eq? 'caar (car exp))
			(eq? 'cadr (car exp))
			(eq? 'cdar (car exp))
			(eq? 'cddr (car exp))
			(eq? 'caaar (car exp))
			(eq? 'caadr (car exp))
			(eq? 'cadar (car exp))
			(eq? 'cdaar (car exp))
			(eq? 'cddar (car exp))
			(eq? 'cdadr (car exp))
			(eq? 'cdddr (car exp))
			(eq? 'caddr (car exp))
			(eq? 'caaaar (car exp))
			(eq? 'caaadr (car exp))
			(eq? 'caadar (car exp))
			(eq? 'cadaar (car exp))
			(eq? 'cdaaar (car exp))
			(eq? 'cddaar (car exp))
			(eq? 'cdadar (car exp))
			(eq? 'cdaadr (car exp))
			(eq? 'caddar (car exp))
			(eq? 'cadadr (car exp))
			(eq? 'caaddr (car exp))
			(eq? 'cdddar (car exp))
			(eq? 'cddadr (car exp))
			(eq? 'cdaddr (car exp))
			(eq? 'cadddr (car exp))
			);end-of-or
			);end-of-and
			#t #f);end-of-if
		))

; Return $t iff list contains only null exoressions and variables
; Examples: (potentially-nulls-args '(x y '() z)) ==> #t	
;			(potentially-nulls-args '(x y d z)) ==> #t	
;			(potentially-nulls-args '(() '() '())) ==> #t	
;			(potentially-nulls-args '(x y 1 '() z)) ==> #f [Because of the number 1]

(define potentially-nulls-args
	(lambda(args)
		(andmap (lambda(e) (or (symbol? e) (null? e) (symbol-null? e))) args)
		))

; Return $t iff list contains at least one element that is, for sure, not a null
; Examples: (non-nulls-args '(x y 1 '() z)) ==> #t	
;			(non-nulls-args '(x y d 'a z)) ==> #t	[Because of the (quote a)]
;			(non-nulls-args '(() '() '())) ==> #f	
;			(non-nulls-args '(x y z)) ==> #f 

(define non-nulls-args
	(lambda(args)
		(ormap (lambda(e) (or (not (variable? e)) (and (not (symbol? e))(not (symbol-null? e))))) args)
		))

; Checks if p is a pair of the from (x . `())

(define (alone? p)
  (and (pair? p)
       (null? (cdr p))))

; NOTICE: This procedure is only relevant in 'non-nulls-args' procedure, so it's not exactly for variables only[nulls too]
; Checks if exp is a variable

(define variable?
	(lambda (exp)
		(if (or (number? exp) (and (pair? exp) (not (eq? 'quote (car exp)))) (boolean? exp) (char? exp) (and (list? exp) (eq? 'quote (car exp)) (not (null? (cadr exp))))) #f #t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;; Fold: Miscellaneous ;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define muls->coefficients
	(lambda(muls)
		(map (lambda(e) (cadr e)) muls)
		))

; Merge muls expressions of the same "variable name"
; Examples: (muls-union `((* 2 x) (* 3 x))) ==> `((* 5 x))
;						`((* 2 x) (* 3 y))) ==> error "cannot union muls of different variables names"

(define muls-union
	(lambda(muls)
		(let* ((coefficients (muls->coefficients muls))
			  (sum-of-coffs (apply + coefficients))) 

			; Let body
			`(* ,sum-of-coffs ,(car (cddar muls)))
			)
		))

(define accumolate-muls
	(lambda(current-mul muls-list)
		(let ((curr (filter (lambda(x) (muls-equal? current-mul x)) muls-list))
			  (rest (filter (lambda(x) (!muls-equal? current-mul x)) muls-list))
			)
		; Let body
		(if (null? rest) `(,(muls-union curr))
		(append `(,(muls-union curr)) (apply append `(,(accumolate-muls (car rest) rest))))
		))
		))

; Merge the mul-expressions only
; Example: `(+ 1 (* 3 x) (* 3 y) 2 (* 2 x) (* 1 y)) ==> `(+ 1 (* 5 x) (+ 4 y))

(define merge-muls
	(lambda (expr)
		(cond ((not (contain-muls expr)) expr)
		(else
		(let* ((muls (filter (lambda(e) (and (list? e) (= 3 (length e)) (eq? '* (car e)))) expr))
			  (rest (filter (lambda(e) (not (and (list? e) (= 3 (length e)) (eq? '* (car e))))) expr))
			  (merged-muls (accumolate-muls (car muls) muls)))
		; Let body
		(if (eq? '* (car merged-muls)) (append rest `(,merged-muls))
			(append rest `(,@merged-muls)))
		)))
		))

; Merge the numbers expressions only
; Example: `(+ 1 x 2 (+ 2 x)) ==> `(+ 3 x (+ 2 x))

(define merge-numbers
	(lambda (expr)
		(let ((numbers (filter number? expr))
			  (rest (filter !number? expr)))
		; Let body
		(append `(+) (append `(,(apply + numbers)) (cdr rest)))
		)
		))

; Convert variables expression to mul-expression
; Example: (vars->mul `(+ 1 x (* 1 y) (* 2 z) w 2)) ==> `(+ 1 (* 1 x) (* 1 y) (* 2 z) (* 1 w) 2)

(define vars->mul
	(lambda(exp)
		(let* ((body (cdr exp))
			   (new-body (map (lambda(e) (if (symbol? e) `(* 1 ,e) e)) body)))

			`(,(car exp) ,@new-body)
	      )))

; Union expressions of the form (cxr^+ ...)

(define union-cxr
  (let ((run

  	 (compose-patterns
      (pattern-rule
      `(car (car (car (car ,(? 'expr)))))
       (lambda (expr) `(caaaar ,expr)))
 	  (pattern-rule
      `(car (car (car (cdr ,(? 'expr)))))
       (lambda (expr) `(caaadr ,expr)))
 	  (pattern-rule
      `(car (car (cdr (car ,(? 'expr)))))
       (lambda (expr) `(caadar ,expr)))
 	  (pattern-rule
      `(car (car (cdr (cdr ,(? 'expr)))))
       (lambda (expr) `(caaddr ,expr)))
 	  (pattern-rule
      `(car (cdr (car (car ,(? 'expr)))))
       (lambda (expr) `(cadaar ,expr)))
      (pattern-rule
      `(car (cdr (car (cdr ,(? 'expr)))))
       (lambda (expr) `(cadadr ,expr)))
      (pattern-rule
      `(car (cdr (cdr (car ,(? 'expr)))))
       (lambda (expr) `(caddar ,expr)))
      (pattern-rule
      `(car (cdr (cdr (cdr ,(? 'expr)))))
       (lambda (expr) `(cadddr ,expr)))
      (pattern-rule
      `(cdr (car (car (car ,(? 'expr)))))
       (lambda (expr) `(cdaaar ,expr)))
      (pattern-rule
      `(cdr (car (car (cdr ,(? 'expr)))))
       (lambda (expr) `(cdaadr ,expr)))
      (pattern-rule
      `(cdr (car (cdr (car ,(? 'expr)))))
       (lambda (expr) `(cdadar ,expr)))
 	  (pattern-rule
      `(cdr (car (cdr (cdr ,(? 'expr)))))
       (lambda (expr) `(cdaddr ,expr)))
      (pattern-rule
      `(cdr (cdr (car (car ,(? 'expr)))))
       (lambda (expr) `(cddaar ,expr)))
      (pattern-rule
      `(cdr (cdr (car (cdr ,(? 'expr)))))
       (lambda (expr) `(cddadr ,expr)))
      (pattern-rule
      `(cdr (cdr (cdr (car ,(? 'expr)))))
       (lambda (expr) `(cdddar ,expr)))
      (pattern-rule
      `(cdr (cdr (cdr (cdr ,(? 'expr)))))
       (lambda (expr) `(cddddr ,expr)))
  	  ;; (car (car (car ..))
 	  (pattern-rule
      `(car (car (car ,(? 'expr))))
       (lambda (expr) `(caaar ,expr)))
 	  ;; (car (car (cdr ..))
 	  (pattern-rule
      `(car (car (cdr ,(? 'expr))))
       (lambda (expr) `(caadr ,expr)))
 	  ;; (car (cdr (car ..))
 	  (pattern-rule
      `(car (cdr (car ,(? 'expr))))
       (lambda (expr) `(cadar ,expr)))
 	  ;; (car (cdr (cdr ..))
      (pattern-rule
      `(car (cdr (cdr ,(? 'expr))))
       (lambda (expr) `(caddr ,expr)))
 	  ;; (cdr (car (car ..))     
 	  (pattern-rule
      `(cdr (car (car ,(? 'expr))))
   	   (lambda (expr) `(cdaar ,expr)))
 	  ;; (cdr (car (cdr ..))	  
      (pattern-rule
      `(cdr (car (cdr ,(? 'expr))))
       (lambda (expr) `(cdadr ,expr)))
 	  ;; (cdr (cdr (car ..))     
 	  (pattern-rule
      `(cdr (cdr (car ,(? 'expr))))
       (lambda (expr) `(cddar ,expr)))
 	  ;; (cdr (cdr (cdr ..))
 	  (pattern-rule
      `(cdr (cdr (cdr ,(? 'expr))))
       (lambda (expr) `(cdddr ,expr)))
  	  ;; (car (car ..))
	   (pattern-rule
   	  `(car (car ,(? 'expr)))
 	   (lambda (expr) `(caar ,expr)))
 	  ;; (car (cdr ..))
 	  (pattern-rule
  	  `(car (cdr ,(? 'expr)))
   	   (lambda (expr) `(cadr ,expr)))
 	  ;; (cdr (car ..))
	  (pattern-rule
      `(cdr (car ,(? 'expr)))
       (lambda (expr) `(cdar ,expr)))
	  ;; (cdr (cdr ..))
 	  (pattern-rule
   	  `(cdr (cdr ,(? 'expr)))
   	   (lambda (expr) `(cddr ,expr)))
       ;; (car ...)
	   (pattern-rule
   	  `(car ,(? 'expr))
 	   (lambda (expr) `(car ,expr)))
 	   ;; (cdr ...)
	   (pattern-rule
   	  `(cdr ,(? 'expr))
 	   (lambda (expr) `(cdr ,expr)))	  

			  )))

    (lambda (e)
      (run e
	   (lambda ()
	     (error 'union-cxr
		    (format "I can't recognize this: ~s" e)))))))

; Create a list of n times occurence of sym
; Example: (list-extend 3 'x `()) ==> `(x x x)

(define list-extend
	(lambda (n sym ls)
		(cond 
			((= n 0) ls)
			(else (list-extend (sub1 n) sym (append ls `(,sym)))) 
			)
		))

; Sort list of symbols
; Example: (symbols-sort `(a x a y b)) ==> `(a z b x y)

(define symbols-sort
	(lambda (ls)
		(map string->symbol
				 (sort string-ci<=? (map symbol->string ls)))
		))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;; Flattens ;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Flatten list

(define (flatten x)
      (cond ((null? x) '())
            ((not (pair? x)) (list x))
            (else (append (flatten (car x))
                          (flatten (cdr x))))))

; Flat all '+' sub-exprs (flat only 1 depth of + sub-expr)!!
; Examples: (flatten-plus `(+ 1 2 (+ 3 x) 5 (+ 2 y))) ==> `(+ 8 3 x 2 y)
;	        (flatten-plus `(+ 1 (+ 2 (+ 1 3) 1))) ==> (+ 1 2 (+ 1 3) 1)

(define flatten-plus
	(lambda (exp)
		(let* (
			   (plus-exprs (filter (lambda(x) (and (list? x) (< 1 (length x)) (eq? '+ (car x)))) exp))
			   (rest (filter (lambda(x) (not (and (list? x) (< 1 (length x)) (eq? '+ (car x))))) exp)) 
			   (flatten-plus-exprs (apply append (map cdr plus-exprs))) ; semi-flatten(depth of flatten=1) sub-exprs of the form (+ _ _ ...)
			)
	 	; Let body
	 	(append rest flatten-plus-exprs)
	 	)		
		))

; Flat all '*' sub-exprs
; Exmaple: (flatten-mul-without-numbers `(+ (* 2 x) (* 3 y)) ==> `(+ x x y y y)

(define flatten-mul-without-numbers
	(lambda (exp)
		(let* (
			   (mul-exprs (filter (lambda(x) (and (list? x) (eq? '* (car x)) (= 3 (length x)))) exp))
			   (rest (filter (lambda(x) (not (and (list? x) (eq? '* (car x)) (= 3 (length x))))) exp)) 
			   (flatten-mul-exprs (flatten (map (lambda (x) (list-extend (cadr x) (caddr x) `())) mul-exprs))) ; flatten sub-exprs of the form (* _ _ ...)
			)
	 	; Let body 
	 	(append rest flatten-mul-exprs)
	 	)		
		))

; Flatten muls of the form (* <number> <var>+)
; Example: (flatten-mul `(* 1 (* 1 x) (* 2 y) (* 1 z) (* 5 t) (* 7 z))) ==> `(* 1 x 2 y z 5 t 7 z)

(define flatten-mul
	(lambda(exp)
		(let* (
			   (muls-exprs (filter (lambda(x) (and (list? x) (eq? '* (car x)))) exp))
			   (rest (filter (lambda(x) (not (and (list? x) (eq? '* (car x))))) exp)) 
			   (flatten-muls-exprs (flatten (map cdr muls-exprs))) ; flatten sub-exprs of the form (* _ _ ...)
			)
	 	; Let body
	 	(append rest flatten-muls-exprs)
	 	)))

; Flatten muls of the form (* 1 _)
; Example: (flatten-junk-mul `(+ 1 (* 1 x) (* 2 y) (* 1 z) (* 5 t) (* 7 z))) ==> `(+ 1 x (* 2 y) z (* 5 t) (* 7 z))

(define flatten-junk-mul
	(lambda(exp)
		(if (not (list? exp)) exp 
			(map (lambda(e) (if (and (list? e) (= 3 (length e)) (eq? '* (car e)) (eq? 1 (cadr e))) (caddr e) e)) exp))
		))

; Flatten canonial appends expressions
; Example: (flatten-append `(append '(1 2) (append x))) ==> `(append '(1 2) x)

(define flatten-append
	(lambda(exp)
		(map (lambda(e) (if (and (list? e) (< 0 (length e)) (eq? 'append (car e))) (if (= 0 (length e)) '() (cdr e)) e)) exp)
		))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;; Folders ;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; "Fold" expressions of the form `(applic (var apend) (...))

(define fold-append
	(lambda (exp)
		(let* ((folded-args (map fold exp))
			   (len (if (list? folded-args) (length folded-args) 0)) ; 0 means nothing
			   (appendable (filter appendable? folded-args))
			   (not-appendable (filter (lambda(e) (not (appendable? e))) folded-args))
	 		   (unioned-appendables (apply append appendable))
			   )
			; Let body
			(cond
				((= 1 len) (if (list? (car folded-args)) `(quote ,(car folded-args)) (car folded-args))) ; This is the case when exp is (append <variable>)
				((null? not-appendable) (if (= 0 (length unioned-appendables)) (append) `(quote ,unioned-appendables))); If every arg is appendable, we just append it
				((null? unioned-appendables) `(append ,@not-appendable))
				(else `(append (quote ,unioned-appendables) ,@not-appendable))
				))
		))

; "Fold" expressions of the form `(string-append ...)

(define fold-string-append
	(lambda (exp)
		(let* ((folded-args (map fold exp))
			   (len (if (list? folded-args) (length folded-args) 0)) ; 0 means nothing
			   (appendable (filter string-appendable? folded-args))
			   (not-appendable (filter (lambda(e) (not (string-appendable? e))) folded-args))
	 		   (unioned-appendables (apply string-append appendable))
			   )
			; Let body
			(cond
				;((= 1 len) (if (list? (car folded-args)) `(quote ,(car folded-args)) (car folded-args))) ; This is the case when exp is (append <variable>)
				((null? not-appendable) (if (and (list? unioned-appendables) (= 0 (length unioned-appendables))) (string-append) unioned-appendables))
				((eq? "" unioned-appendables) `(string-append ,@not-appendable))
				(else `(string-append ,unioned-appendables ,@not-appendable))
				))
		))

; "Fold" expressions of the form `(+ ...)

(define fold-plus
	(lambda (exp)	
		(let* 
			  ((folded-body (flatten-plus (map fold exp)))
			  (constants (get-constants-mul folded-body))
			  (non-constants (get-non-constants-mul folded-body))
			  (sum-of-constants (apply + constants))
			  (res 
			    (cond 
				 ((null? non-constants) sum-of-constants) ; (without operator sign - constants only)
				 ((= sum-of-constants 0) ; [(+) ==> 0 , (apply + `()) ==> 0]
				 (if (alone? non-constants) (car non-constants)  
				 	; else
				 	(let ((b (flatten-junk-mul (merge-muls (vars->mul `(+ ,@non-constants)))))) 
						(if (and (list? b) (= 2 (length b))) (cadr b) b))))

				 (else 
			     	(flatten-junk-mul (merge-muls (vars->mul `(+ ,sum-of-constants ,@non-constants))))
				 ))))
			  res
			)))

; "Fold" expressions of the form `(applic (var *) (...))

(define fold-mul
	(lambda (exp)
		(let* 
			  ((folded-body (flatten-mul (map fold exp)))
			  (constants (get-constants-mul folded-body))
			  (non-constants (get-non-constants-mul folded-body))
			  (product-of-constants (apply * constants))
			  (res 
			    (cond 
				 ((null? non-constants) product-of-constants) ; (without operator sign - constants only)
				 ((= product-of-constants 0) 0)
				 ((and (= product-of-constants 1) (= 1 (length non-constants)) (car non-constants)))
			     ((null? constants) `(* ,@exp)) ; There's nothing to fold here [(fold `(* x x x))==>`(* x x x)]

				 (else 
					`(* ,product-of-constants ,@non-constants)

				 ))))
			  res
			)))

; "Fold" expressions of the form `(cons ...) 

(define fold-cons
	(lambda(exp)

		(let* ((left (fold (cadr exp)))
			   (right (fold (caddr exp))))

				(cond
					((and (not (ifoldable left)) (not (ifoldable right))) (cons left right))
					((and (ifoldable right) (not (ifoldable left))) `(cons ,left ,right))
					((and (ifoldable left) (not (ifoldable right))) `(cons ,left ,right))
					(else `(cons ,left ,right))
				))
		))

; Fold expressions of the form (if test dit dif)

(define fold-if-else
	(lambda(exp)
		(let* ((test (fold (cadr exp)))
			   (dit (fold (caddr exp)))
			   (dif (fold (cadddr exp))))

				(cond
					; If dit and dif are equals, then the 'test' means nothing and we can return one of them
					((and (not (boolean? test)) (equal? dif dit)) dit)
					; We don't know for sure what we need to return, then leave it as is
					((and (not (boolean? test)) (not (equal? dif dit))) `(if ,test ,dit ,dif))
					; Else, test is boolean and we know what we need to return
					(else (if test dit dif))
					))))

; Fold expressions of the form (if test dit)

(define fold-if
	(lambda(exp)
		(let* ((test (fold (cadr exp)))
			   (dit (fold (caddr exp))))

				(cond
					; If test is not aboolean, then there is nothing to fold here
					((not (boolean? test)) `(if ,test ,dit))
					; Else, test is a boolean
					(else (if test dit))
					))))

; Fold expressions of the form (string? _)

(define fold-string?
	(lambda(exp)
		(let* ((param (fold (cadr exp))))
			(cond
				((symbol? param) `(string? ,param))
				((and (list? param) (< 0 (length param)) (eq? 'string-append (car param))) #t)
				(else (string? param))
				))))

; Fold expressions of the form (number? _)

(define fold-number?
	(lambda(exp)
		(let* ((folded-param (fold (cadr exp)))
			   (param (cadr exp)))
			(cond
				((and (list? param) (= 3 (length param)) (eq? '* (car param)) (number? (cadr param)) (= 1 (cadr param)) (symbol? (caddr param))) #t)
				(else
			(if (symbol? folded-param) `(number? ,folded-param) (if (or (and (list? folded-param) (or (eq? '+ (car folded-param)) (eq? '* (car folded-param)))) (number? folded-param)) #t #f)))
				);end-of-else
				);end-of-cond
				))

; Fold expressions of the form (zero? _)

(define fold-zero?
	(lambda(exp)
		(let* ((param (fold (cadr exp))))
			(if (symbol? param) `(zero? ,param) (if (number? param) (zero? param) #f)))
				))

; Fold expressions of the form (list ...)

(define fold-list
	(lambda(exp)
		(let* ((folded-args (map fold exp)))
			(if (ormap (lambda(e) (or (application-list? e) (symbol? e))) folded-args) `(list ,@folded-args) (car (list folded-args)))
		)
		))

; Fold expressions of the form (cxr ...) [car/cdr only]

(define fold-cxr
	(lambda (exp)
		(let* ((op (car exp))
			 (folded-param (fold (cadr exp)))
			 (len (if (list? folded-param) (length folded-param) 0))) ; 0 means nothing.
			; Let body
			(cond
				; (car (fold param)) ==> (car <variable>)
				((symbol? folded-param) `(,op ,folded-param))
				; folded-param is a 'cons' expression
				((and (list? folded-param) (eq? 'cons (car folded-param))) 
					; Then, if it's expr of the form (cons x y) we fold it. Otherwise leave it as is
					(if (> len 2) (if (eq? 'car op) (cadr folded-param) (caddr folded-param)) `(,op ,folded-param)))
				; folded-param is a 'list' expression
				((and (list? folded-param) (eq? 'list (car folded-param))) 
					; Then, if it's expr of the form (list x) we fold it. Otherwise leave it as is
					(if (> len 1) (if (eq? 'car op) (cadr folded-param) (cddr folded-param)) `(,op ,folded-param)))
				; If folded-param is an 'cxr' expression, then there's nothing to fold here
				((cxr-application? folded-param) `(,op ,folded-param))
				; Else we can just apply this op of the folded-param
				(else (if (eq? 'car op) (car folded-param) (cdr folded-param)))

				))
		))

; Fold expressions of the form (null? ...)

(define fold-null?
	(lambda(exp)
		(let ((folded-param (fold (cadr exp))))

			(cond
				; If it's variable, then we leave it as is
				((symbol? folded-param) `(null? ,folded-param))
				; Here we handle the confusing case, in which param is 'append' expression:
				; Case1: In the 'append' expr, if at least one of the params isn't a null or a variable, we know it's not a null
				((and (list? folded-param) (> (length folded-param) 0) (eq? 'append (car folded-param)) (non-nulls-args folded-param)) #f)
				; Case2: In the 'append' expr, if every param is a variable or a null, we leave it as is[it is petentially null]
				((and (list? folded-param) (> (length folded-param) 0) (eq? 'append (car folded-param)) (potentially-nulls-args folded-param)) `(null (append ,@folded-param)))
				; Here we handle 'if' expression:
				; Case1: We can't know for sure that it will return null
				((and (list? folded-param) (> (length folded-param) 1) (eq? 'if (car folded-param)) (potentially-nulls-args (cddr folded-param))) `(null? ,folded-param))
				; Case2: If we know for sure that it will return somthing that is NOT null, we can return #f
				((and (list? folded-param) (> (length folded-param) 1) (eq? 'if (car folded-param)) (non-nulls-args (list (caddr folded-param))) (non-nulls-args (cdddr folded-param))) #f)
				; Else we can evaluating it normally
				(else (null? folded-param))
				))
		))

; This is the main folder

(define fold

  (let ((run
	 (compose-patterns
	  ;; constant
	  (pattern-rule
	   (? 'c simple-const?)
	   (lambda (c) c))
	  ;; variable
	  (pattern-rule
	   (? 'v var?)
	   (lambda (v) v));`(var ,v)))
	  ;; quote - no args
	  (pattern-rule
	   `(quote)
	   (lambda () (list)))
	  ;; quote
	  (pattern-rule
	   `(quote ,(? 'c (lambda(e) (not (list? e)))))
	   (lambda (c) `(quote ,c)));`(quote ,c)))
	  ;; string?
	  (pattern-rule
	   `(string? ,(? 'c))
	   (lambda (c) (fold-string? `(string? ,c))))
	  ;; number?
	  (pattern-rule
	   `(number? ,(? 'c))
	   (lambda (c) (fold-number? `(number? ,c))))
	  ;; zero?
	  (pattern-rule
	   `(zero? ,(? 'c))
	   (lambda (c) (fold-zero? `(zero? ,c))))
	  ;; append - no arg
	  (pattern-rule
	   `(append)
	   (lambda ()
	   (append)))
	  ;; append - one or more args
	  (pattern-rule
	   `(append . ,(? 'args list?))
	   (lambda (args)
	     (fold-append args)))
	  ;; string-append - no arg
	  (pattern-rule
	   `(string-append)
	   (lambda ()
	   (string-append)))
	  ;; string-append - one or more args
	  (pattern-rule
	   `(string-append . ,(? 'args list?))
	   (lambda (args)
	     (fold-string-append args)))
	  ;; if-then
	  (pattern-rule
	   `(if ,(? 'test) ,(? 'dit))
	   (lambda (test dit)
	     (fold-if `(if ,test ,dit))))
	  ;; if-then-else
	  (pattern-rule
	   `(if ,(? 'test) ,(? 'dit) ,(? 'dif))
	   (lambda (test dit dif)
	     (fold-if-else `(if ,test ,dit ,dif))))
	  ;; (cons `() `())
	  (pattern-rule
	   `(cons ,(? 'arg1 symbol-null?) ,(? 'arg2 symbol-null?))
	   (lambda (arg1 arg2) (cons `() `())))
	  ;; (cons `() _) [_ != `()]
	  (pattern-rule
	   `(cons ,(? 'arg1 symbol-null?) ,(? 'arg2 (lambda(e) (not (symbol-null? e)))))
	   (lambda (arg1 arg2) (fold-cons `(cons '() ,arg2))))		
	  ;; (cons _ `()) [_ != `()]
	  (pattern-rule
	   `(cons ,(? 'arg1 (lambda(e)(not (symbol-null? e)))) ,(? 'arg2 symbol-null?))
	   (lambda (arg1 arg2) (list (fold arg1))))
	  ;; cons
	  (pattern-rule
	   `(cons ,(? 'test) ,(? 'dit))
	   (lambda (test dit) (fold-cons `(cons ,test ,dit))))
	  ; Maybe junk
	  (pattern-rule
	   `(,(? 'test null?))
	   (lambda (test) `()))	
	  ; Maybe junk
	  (pattern-rule
	   `(? `t null?) 
	   (lambda (t) `()))	
	  ;;null expression
	  (pattern-rule
	   `(null? ,(? 't)) 
	   (lambda (t) (fold-null? `(null? ,t))))

      (pattern-rule
      `(car (car (car (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
 	  (pattern-rule
      `(car (car (car (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
 	  (pattern-rule
      `(car (car (cdr (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
 	  (pattern-rule
      `(car (car (cdr (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
 	  (pattern-rule
      `(car (cdr (car (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(car (cdr (car (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(car (cdr (cdr (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(car (cdr (cdr (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (car (car (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (car (car (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (car (cdr (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
 	  (pattern-rule
      `(cdr (car (cdr (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (cdr (car (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (cdr (car (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (cdr (cdr (car ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))
      (pattern-rule
      `(cdr (cdr (cdr (cdr ,(? 'expr)))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))))

 	  ;; (car (car (car ..))
 	  (pattern-rule
      `(car (car (car ,(? 'expr))))
       (lambda (expr) (union-cxr `(car ,(fold-cxr (fold-cxr `(car ,(fold-cxr `(car ,expr)))))))))
 	  ;; (car (car (cdr ..))
 	  (pattern-rule
      `(car (car (cdr ,(? 'expr))))
       (lambda (expr) (union-cxr `(car ,(fold-cxr (fold-cxr `(car ,(fold-cxr `(cdr ,expr)))))))))
 	  ;; (car (cdr (car ..))
 	  (pattern-rule
      `(car (cdr (car ,(? 'expr))))
       (lambda (expr) (union-cxr `(car ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(car ,expr)))))))))
 	  ;; (car (cdr (cdr ..))
      (pattern-rule
      `(car (cdr (cdr ,(? 'expr))))
       (lambda (expr) (union-cxr `(car ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))
 	  ;; (cdr (car (car ..))     
 	  (pattern-rule
      `(cdr (car (car ,(? 'expr))))
   	   (lambda (expr) (union-cxr `(cdr ,(fold-cxr (fold-cxr `(car ,(fold-cxr `(car ,expr)))))))))
 	  ;; (cdr (car (cdr ..))	  
      (pattern-rule
      `(cdr (car (cdr ,(? 'expr))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr (fold-cxr `(car ,(fold-cxr `(cdr ,expr)))))))))
 	  ;; (cdr (cdr (car ..))     
 	  (pattern-rule
      `(cdr (cdr (car ,(? 'expr))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(car ,expr)))))))))
 	  ;; (cdr (cdr (cdr ..))
 	  (pattern-rule
      `(cdr (cdr (cdr ,(? 'expr))))
       (lambda (expr) (union-cxr `(cdr ,(fold-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))))

	  ;; (car (car ..))
	   (pattern-rule
   	  `(car (car ,(? 'expr)))
 	   (lambda (expr) (union-cxr (fold-cxr `(car ,(fold-cxr `(car ,expr)))))))
 	  ;; (car (cdr ..))
 	  (pattern-rule
  	  `(car (cdr ,(? 'expr)))
   	   (lambda (expr) (union-cxr (fold-cxr `(car ,(fold-cxr `(cdr ,expr)))))))
 	  ;; (cdr (car ..))
	  (pattern-rule
      `(cdr (car ,(? 'expr)))
       (lambda (expr) (union-cxr (fold-cxr `(cdr ,(fold-cxr `(car ,expr)))))))
	  ;; (cdr (cdr ..))
 	  (pattern-rule
   	  `(cdr (cdr ,(? 'expr)))
   	   (lambda (expr) (union-cxr (fold-cxr `(cdr ,(fold-cxr `(cdr ,expr)))))))

       ;; (car ...)
	   (pattern-rule
   	  `(car ,(? 'expr))
 	   (lambda (expr) (fold-cxr `(car ,expr))))
 	   ;; (cdr ...)
	   (pattern-rule
   	  `(cdr ,(? 'expr))
 	   (lambda (expr) (fold-cxr `(cdr ,expr))))
      ;; list - no args
	  (pattern-rule
	   `(list)
	   (lambda () (list)))
	  ;; list 
	  (pattern-rule
	   `(list . ,(? 'args list?))
	   (lambda (args) (fold-list args)))
      ;; * - no args
	  (pattern-rule
	   `(*)
	   (lambda () 1))
	  ;; * 
	  (pattern-rule
	   `(* . ,(? 'args list?))
	   (lambda (args) (fold-mul args)))
      ;; + - no args
	  (pattern-rule
	   `(+)
	   (lambda () 0))
	  ;; + 
	  (pattern-rule
	   `(+ . ,(? 'args list?))
	   (lambda (args) (fold-plus args)))
	  ;; add1
	  (pattern-rule
	   `(add1 . ,(? 'arg))
	   (lambda (arg) (fold `(+ 1 ,@arg))))
	  ;; sub1
	  (pattern-rule
	   `(sub1 . ,(? 'arg))
	   (lambda (arg) (fold `(+ ,@arg -1))))

	  (pattern-rule
	   `(? 'a (lambda(e) #t))
	   (lambda (a) a))

	  )))

    (lambda (e)
      (run e
	   (lambda ()
	     (eval e))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Ass3: Annotating variables with their lexical address ;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Return TRUE iff tagged expressions is tagged by 'tag'
; Examples: (tagged-by? 'const `(const 2)) ==> #t
;			(tagged-by? 'var `(const 2)) ==> #f

(define tagged-by?
  (lambda (tag te)
    (if (pair? te)
        (eq? tag (car te))
        #f)))


(define search
        (lambda (a s ret-min ret-nf)
                (cond ((null? s) (ret-nf))
                        ((eq? (car s) a) (ret-min 0))
                        (else (search a (cdr s)
                                        (lambda (min)
                                                        (ret-min (+ 1 min)))
                                        ret-nf)))))

(define searchs
        (lambda (a env ret-maj+min ret-nf)
                (if (null? env)
                        (ret-nf)
                        (search a (car env)
                                (lambda (min)
                                                (ret-maj+min 0 min))
                                (lambda ()
                                                (search a (cdr env)
                                                        (lambda (maj min)
                                                                (ret-maj+min (+ 1 maj) min))
                                                        ret-nf))))))



(define run
        (lambda (pe params env)
                (cond   ((tagged-by? 'const pe) pe)
                                ((tagged-by? 'var pe)
                                        (with pe
                                                (lambda (_ v)
                                                        (search v params
                                                                (lambda (min) `(pvar ,v ,min))
                                                                (lambda() (searchs v env
                                                                        (lambda (min maj) `(bvar ,v ,min ,maj))
                                                                        (lambda () `(fvar ,v)) ))))))
                                ((tagged-by? 'if3 pe)
                                        (with pe
                                                (lambda (_ test dit dif)
                                                        `(if3 ,(run test params env) ,(run dit params env) ,(run dif params env)))))
                                ((tagged-by? 'lambda-simple pe)
                                        (with pe
                                                (lambda (_ args body)
                                                        `(lambda-simple ,args ,(run body args (cons params env))))))

                                ((tagged-by? 'lambda-opt pe)
                                        (with pe
                                                (lambda (_ args opt body)
                                                        (let ((args2 `(,@args ,opt)))
                                                        `(lambda-opt ,args ,opt ,(run body args2 (cons params env)))))))

                                ((tagged-by? 'lambda-variadic pe)
                                        (with pe
                                                (lambda (_ args body)
                                                        `(lambda-variadic ,args ,(run body (list args) (cons params env))))))

                                ((tagged-by? 'define pe)
                                        (with pe
                                                (lambda (_ var exp)
                                                        `(define ,(run var params env) ,(run exp params env)))))
                                ((or (tagged-by? 'applic pe) )
                                        (with pe
                                                (lambda (tag proc args)
                                                        `(,tag ,(run proc params env) ,(map (lambda (ex)
                                                                                                                                        (run ex params env)) args)))))
                                ((tagged-by? 'seq pe)
                                        (with pe
                                                (lambda (_ exps)
                                                        `(seq ,(map (lambda (ex)
                                                                                (run ex params env)) exps)))))
                                ((tagged-by? 'or pe)
                                        (with pe
                                                (lambda (_ exps)
                                                        `(or ,(map (lambda (ex)
                                                                                (run ex params env)) exps)))))

                                (else pe) )))

(define pe->lex-pe
        (letrec ((run
             (lambda (pe params env)
                   (cond 	
                   			((tagged-by? 'const pe) pe) 
                            ((tagged-by? 'var pe)
                                                        (with pe
                                                                (lambda (_ v)
                                                                        (search v params
                                                                                (lambda (min) `(pvar ,v ,min))
                                                                                (lambda() (searchs v env
                                                                                        (lambda (min maj) `(bvar ,v ,min ,maj))
                                                                                        (lambda () `(fvar ,v)) ))))))
                            ((tagged-by? 'if3 pe)
                                           (with pe
                                                    (lambda (_ test dit dif)
                                                            `(if3 ,(run test params env) ,(run dit params env) ,(run dif params env)))))
                            ((tagged-by? 'lambda-simple pe)
                                            (with pe
                                                    (lambda (_ args body)
                                                           `(lambda-simple ,args ,(run body args (cons params env))))))

                            ((tagged-by? 'lambda-opt pe)
                                            (with pe
                                                    (lambda (_ args opt body)
                                                             (let ((args2 `(,@args ,opt)))
                                                            `(lambda-opt ,args ,opt ,(run body args2 (cons params env)))))))

                            ((tagged-by? 'lambda-variadic pe)
                                            (with pe
                                                    (lambda (_ args body)
                                                            `(lambda-variadic ,args ,(run body (list args) (cons params env))))))

                            ((tagged-by? 'define pe)
                                             (with pe
                                                (lambda (_ var exp)
                                                     `(define ,(run var params env) ,(run exp params env)))))
                            ((or (tagged-by? 'applic pe))
                                             (with pe
                                                (lambda (tag proc args)
                                                     `(,tag ,(run proc params env) ,(map (lambda (ex)
                                                                                                   (run ex params env)) args)))))
                             ((or (tagged-by? 'tc-applic pe))
                                             (with pe
                                                (lambda (tag proc args)
                                                     `(,tag ,(run proc params env) ,(map (lambda (ex)
                                                                                                   (run ex params env)) args)))))
                            ((tagged-by? 'seq pe)
                                             (with pe
                                                (lambda (_ exps)
                                                     `(seq ,(map (lambda (ex)
                                                                   (run ex params env)) exps)))))
                                                ((tagged-by? 'or pe)
                                                     (with pe
                                                                (lambda (_ exps)
                                                                        `(or ,(map (lambda (ex)
                                                                                                (run ex params env)) exps)))))

                                                (else (error 'pe->lex-pe (format "~s is not legal parsed expression" pe)))) )))

        (lambda (pe)
                (run pe '() '()))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;; Ass3: Annotating tail calls ;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define annotate-tc
  (letrec ((divide-tc
            (lambda (pe new-tc?)
              `(,@(map (lambda (x)
                         (run x #f))
                       (list-head (cadr pe) (- (length (cadr pe)) 1))) ,(run (car (reverse (cadr pe))) new-tc?))))

           (all-but-last
            (lambda (pe func tc?)
              (if (null? (cdr pe))
                  (func (car pe) tc?)
                  (cons (func (car pe) #f) (all-but-last (cdr pe) func tc?)))))
           (run
            (lambda (pe tc?)
              (cond ((tagged-by? 'const pe) pe)
                    ((tagged-by? 'fvar pe) pe)
                    ((tagged-by? 'var pe) pe)
                    ((tagged-by? 'pvar pe) pe)
                    ((tagged-by? 'bvar pe) pe)
                    ((tagged-by? 'if3 pe)
                     (with pe
                           (lambda (_ test dit dif)
                             `(if3 ,(run test #f)
                                    ,(run dit tc?)
                                    ,(run dif tc?)))))
                    ((tagged-by? 'lambda-simple pe)
                     (with pe
                           (lambda (tag param body)
                             `(,tag ,param ,(run body #t)))))
                    ((tagged-by? 'lambda-opt pe)
                     (with pe
                           (lambda (tag param opt body)
                             `(,tag ,param ,opt ,(run body #t)))))
                    ((tagged-by? 'lambda-variadic pe)
                     (with pe
                           (lambda (tag param body)
                             `(,tag ,param ,(run body #t)))))
                    ((tagged-by? 'define pe)
                     (with pe
                           (lambda (tag var dpe)
                             `(,tag ,var ,(run dpe #f)))))
                    ((tagged-by? 'applic pe)
                     (if (eq? tc? #f)
                         (with pe
                               (lambda (_ proc expList)
                                 `(applic ,(run proc #f)
                                          ,(map (lambda (exp)
                                                  (run exp #f)) expList))))
                         (with pe
                               (lambda (_ proc expList)
                                 `(tc-applic ,(run proc #f)
                                             ,(map (lambda (exp)
                                                     (run exp #f)) expList))))))
                    ((tagged-by? 'seq pe)  `(seq ,(divide-tc pe tc?)))
                    ((tagged-by? 'or pe) `(or ,(divide-tc pe tc?)))
                    (else (error 'annotate-tc (format "~s is not legal parsed expression" pe)))))))
    (lambda (pe)
      (run pe #f)))) 


(define test
  (lambda (e)
    (annotate-tc
      (pe->lex-pe
	(parse e)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Assignment 4: Final Project ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;; Ass4: Global Variables ;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; LEASHLIMMMMMMMMMMMMM*********************
(define error
	(lambda()
		(string-append
			"\t/* error_no-such-type */\n"
			"ERROR_NST:\n"
			(code-gen-string->chars "Error: no such type" 18)
			"\tPUSH(IMM(19));\n"
			"\tCALL(MAKE_SOB_STRING);\n"
			"\tDROP(IMM(20));\n"
			"\tPUSH(R0);\n"
			"\tCALL(WRITE_SOB_STRING);\n"
			"return 1;"
			"\t/* error_undefined-variable */\n"
			"ERROR_UNDEFINED_VAR:\n"
			(code-gen-string->chars "Error: variable " 15)
			"\tPUSH(IMM(16));\n"
			"\tCALL(MAKE_SOB_STRING);\n"
			"\tDROP(IMM(17));\n"
			"\tPUSH(R0);\n"
			"\tCALL(WRITE_SOB_STRING);\n"
			"\tDROP(IMM(1));\n"
			"\tPUSH(R1);\n"
			"\tCALL(WRITE_SOB);\n"
			"\tDROP(IMM(1));\n"
			(code-gen-string->chars " is undefined." 13)
			"\tPUSH(IMM(14));\n"
			"\tCALL(MAKE_SOB_STRING);\n"
			"\tDROP(IMM(15));\n"
			"\tPUSH(R0);\n"
			"\tCALL(WRITE_SOB_STRING);\n"
			"return 1;"
		)))

; Here we define a global variable which stores the current free unique-tag

(define unique-tag 0)


; Here we define a global variable which stores the first free address for the buckets.
; As appears from Mayer's tamplate(user-scheme-code.c), the initial value is 16.

(define buckets-first-free-address 16)

; Here we define a global list of stuctures. each struct is a list of length 3,
; of the form '(tag value address)
	
(define consts-struct-list '())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;; Ass4: Miscellaneous ;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ******LEASHLIM******
(define pair->string
	(lambda (pair)
"#t"
		))

; complex-const?(pe) procedure.
; Takes expression and return #t iff its type is one of the following: 
; Symbol, Pair or Vector.
;
; Type: [T -> Boolean]
; Examples: (complex-const? (1 . 2)) ==> #t
;			(complex-const? "x") ==> #f

(define complex-const?
	(lambda (exp)
		(if 
			(or (symbol? exp) (pair? exp) (vector? exp))
			#t
			#f
			)
		))

; attach-tag-and-address(tmp lst addr) procedure.
; This procedure recursivley maps over the constants list and covert them to the constant-struct(i.e. '(Tag Value address)).
; 
; Type: [List(T)*List(T)*Number -> List(List(T))]
; Examples: (attach-tag-address '() '(3 "2") 16) ==> '('('number 3 16) '('string "2" 19))

(define attach-tag-and-address
	(lambda (tmp lst current-addr)
		(let ((val (if (null? lst) lst (car lst))))
			(cond
				; Base Case: Update global var and return 
				((null? lst) (begin (set! buckets-first-free-address current-addr) tmp))
				; The current-addr specify the address of the expected bucket, then, for strings, 
				; we need to take into account the length of the string.
				((string? val) 
					(attach-tag-and-address (append tmp (list (list 'string val current-addr))) (cdr lst) 
						(+ (string-length val) current-addr 2))) ; New current-address
				((number? val)
					(attach-tag-and-address (append tmp (list (list 'int val current-addr))) (cdr lst)
						(+ current-addr 2))) ; New current-address
				((char? val)
					(attach-tag-and-address (append tmp (list (list 'char val current-addr))) (cdr lst)
						(+ current-addr 2))) ; New current-address
				((symbol? val)
					(attach-tag-and-address (append tmp (list (list 'symbol val current-addr))) (cdr lst)
						(+ current-addr 2))) ; New current-address	
				((vector? val) 
					(attach-tag-and-address 
						(append tmp (list (list 'vector val current-addr))) 
						(cdr lst) 
						(+ current-addr (+ 2 (vector-length val)))))	
				; Note: pair contains two elements, then we need to allocate one more WORD in memory	
				((pair? val)
					(attach-tag-and-address (append tmp (list (list 'pair val current-addr))) (cdr lst)
						(+ current-addr 3))) ; New current-address	
			))
		))

; duplicates-and-bool-filter(tmp lst) procedure.
; Remove all occurrences of booleans or duplicates constants
;
; Type: [List(T)*List(T) -> List(T)]
; Examples: see tests file

(define duplicates-and-bool-filter
	(lambda (tmp lst)
		(cond
			((null? lst) tmp)
			((or (null? (car lst)) (boolean? (car lst)) (equal? (car lst) *void-object*)
					((lambda (exp b) 
						(if (list? (member exp b)) #t #f)) (car lst) tmp))
				(duplicates-and-bool-filter tmp (cdr lst)))
			(else (duplicates-and-bool-filter (append tmp (list (car lst))) (cdr lst)))
		)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;; Ass4: Constructures ;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; make-consts-struct-list(srcFile) procedure.
; Takes list of parsed sexprs as an input, and return a list of structures. each struct
; is a list of length 3, of the form '(tag value address)
;
; Type: [List(Sexpr) -> List(List(T))]
; Examples: see tests file.

(define make-consts-struct-list
	(lambda (sxprList)
		(let ((b (duplicates-and-bool-filter '() (make-consts-struct-list-rec '() sxprList)))) ; Remove duplicates after creation
			; Body of let
			(attach-tag-and-address '() b 16) ; Here's we are actually generates the structs(16 is the initial first-free-address) 
		)))

; make-consts-struct-list-rec(tmp sxprList) procedure.
; This procedure helps to creates the structs list recursivley
;
; Type: [List(Sexprs)*List(Sexprs) -> List(List(T))]
; Examples: see tests file

(define make-consts-struct-list-rec
	(lambda (tmp sxprList)
		(cond
			((or (not (list? sxprList)) (null? sxprList)) tmp)
			((tagged-by? 'fvar sxprList) (append tmp (topological-sort (cadr sxprList))))
			((tagged-by? 'const sxprList) 
				(if (complex-const? (cadr sxprList)) 
					(append tmp (topological-sort (cadr sxprList)))
					; Else, there's no need to sort it
					(append tmp (cdr sxprList))))
			(else (make-consts-struct-list-rec (make-consts-struct-list-rec tmp (car sxprList)) (cdr sxprList))))
		))

; make-const-buckets(lst) procedure.
; Input: List of constants structs(as defined in make-consts-struct-list)
; Output: Strig of the assembly code that generate the constants buckets.
;
; Type: [List(List(T)) -> String]
; Examples: see tests file

(define make-const-buckets
	(lambda (lst)
		(if (null? lst) "" 
		; Else
		(let ( 
			(tag (caar lst)) ; Tag from the struct(see struct definition in 'make-consts-struct-list')
			(val (cadar lst)) ; Value from the struct
			(addr (caddar lst))) ; Address from the struct
			; Body-of-let
			(cond

				; Generate assembly code that generates bucket for string object.
				; The string stores as a sequence of chars, meaning that the bucket's form is as follows:
				; first cell: type(T_STRING), second cell: the length of the string,
				; third cell: char #1, forth cell: char #2, ..., etc.
				((eq? tag 'string)
					(string-append 
					"\t/* Assembly code that generates the SOB string, using malloc to allocate memory: \"" val "\" */\n"
					(code-gen-string->chars val (sub1 (string-length val)))
					"\tPUSH(IMM(" (number->string (string-length val)) "));\n"
					"\tCALL(MAKE_SOB_STRING);\n"
					"\tDROP(IMM(" (number->string (add1 (string-length val))) "));\n"
					(make-const-buckets (cdr lst)))) ; Recursive call

				; Generate assembly code that generates bucket for char object.
				; The bucket's form is as follows:
				; first cell: type(T_CHAR), second cell: the char value itself.
				((eq? tag 'char)
					(string-append
					"\t/* Assembly code that generates the SOB char, using malloc to allocate memory: " (string val) " */\n"
					"\tPUSH(IMM(" (number->string (char->integer val)) "));\n"
					"\tCALL(MAKE_SOB_CHAR);\n"
					"\tDROP(IMM(1));\n"
					(make-const-buckets (cdr lst)))) ; Recursive call

				; Generate assembly code that generates bucket for integer object.
				; The bucket's form is as follows:
				; first cell: type(T_INTEGER), second cell: the int value itself.
				((eq? tag 'int)
					(string-append
					"\t/* Assembly code that generates the SOB integer, using malloc to allocate memory: " (number->string val) " */\n"
					"\tPUSH(IMM(" (number->string val) "));\n"
					"\tCALL(MAKE_SOB_INTEGER);\n"
					"\tDROP(IMM(1));\n"
					(make-const-buckets (cdr lst)))) ; Recursive call

				; Generate assembly code that generates bucket for pair object.
				; The bucket's form is as follows:
				; first cell: type(T_PAIR), second cell: a pointer to the bucket of the first element,
				; third cell: a pointer to the bucket of the second element.
				;
				; NOTE: In make-const-buckets we used topological-sort on pairs objects,
				; meaninig that, in the constants-struct-list, the structures of the two elements in the pair objects appears
				; before the struct of the pair object itself, meaning that, at this point, we already created the buckets
				; of the elements that in the pair object. Therefore, we pushs into the stack the addresses of the elements.
				((eq? tag 'pair)
					(string-append
					"\t/* Assembly code that generates the SOB pair, using malloc to allocate memory: \"" (pair->string val) "\" */\n"
					"\tPUSH(" (number->string (if (null? (cdr val)) 11 (get-address consts-struct-list (cdr val)))) ");\n"
					"\tPUSH(" (number->string (get-address consts-struct-list (car val))) ");\n"						
					"\tCALL(MAKE_SOB_PAIR);\n"
					"\tDROP(IMM(2));\n"
					(make-const-buckets (cdr lst)))) ; Recursive call

				((eq? tag 'vector)
					(string-append
						(cg-vector-elements val (sub1 (vector-length val)))
						"\tPUSH(IMM(" (number->string (vector-length val)) "));\n"
						"\tCALL(MAKE_SOB_VECTOR);\n"
						"\tDROP(IMM(" (number->string (add1 (vector-length val))) "));\n"
						(make-const-buckets (cdr lst))
				))

				; Generate assembly code that generates bucket for symbol object
				; (NOTE: it's not the bucket in the SYMBOL TABLE!).
				; The bucket's form is as follows:
				; first cell: type(T_SYMBOL), second cell: null pointer(explanation below).
				;
				; NOTE: The secend cell will points to the corresponding bucket in the SYMBOL TABLE.
				; Since, at this point, we don't has a symbol table, we leave it with temporary value
				; (we will fix it at symbol table creation)
				((eq? tag 'symbol) (string-append
				    "\t/* Assembly code that generates SOB symbol, using malloc to allocate memory: */\n"
					"\tPUSH(IMM(2));\n"
					"\tCALL(MALLOC);\n"
					"\tDROP(1);\n"
					"\tMOV(IND(R0), T_SYMBOL);\n"
					"\tMOV(INDD(R0,1), IMM(0));\n"
					(make-const-buckets (cdr lst))))))) ; Recursive call
	))

; make-symbol-table(lst current-bucket) procedure.
; Generate string of the assembly code that generate the symbols buckets in the SYMBOL TABLE.
;
; Type: [List(List(T))*Number -> String]
; Examples: see tests file

(define make-symbol-table
	(lambda (lst current-bucket)
		(if (null? lst) "" 
		; Else
		(let ( 
			(tag (caar lst)) ; Tag from the struct(see struct definition in 'make-consts-struct-list')
			(val (cadar lst)) ; Value from the struct
			(addr (caddar lst))) ; Address from the struct
			
			; Generate assembly code that generates bucket in the SYMBOL TABLE,
			; and update the second cell(the pointer) of the corresponding bucket
			; we've already created in 'make-const-buckets' to points to THIS bucket.
			; The bucket's form is as follows:
			; first cell: a pointer to the corresponding STRING bucket we've already created(i.e. 
			; if the symbol is x, then points to the bucket of "x"),
			; second cell: a pointer to the next bucket in the SYMBOL TABLE(we generating a linked-list of buckets),
			; third cell: NULL pointer for now(it will be assign to const bucket -its value- in code-gen-define).
			(string-append
				"\t/* Assembly code that stores bucket in the symbol table. */\n"
				"\tPUSH(IMM(3));\n"
				"\tCALL(MALLOC);\n"
				"\tMOV(IND(" (number->string (add1 addr)) "),R0);\n"
				"\tMOV(IND(R0)," (number->string (get-address consts-struct-list (symbol->string val))) ");\n"
				"\tMOV(INDD(R0,1)," (number->string (if (null? (cdr lst)) 0 (+ current-bucket 3))) ");\n"
				"\tMOV(INDD(R0,2),IMM(0));\n"
				(make-symbol-table (cdr lst) current-bucket))))
))

;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Ass4: Setters ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

; inc-unique-tag(tag) procedure.
; Increment the value of the global variable 'unique-tag' by one.
;
; Type: [Empty -> Void]
; Examples: #t

(define inc-unique-tag
	(lambda ()
		(set! unique-tag (add1 unique-tag))))

;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Ass4: Getters ;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;

; get-address(lst val) procedure.
; Takes constant value as an input, and travers recursivley on the global list 'consts-struct-list'
; to find its address
; Type: [T -> Number]
; Example: see tests file.

(define get-address
	(lambda (lst val) 
		(cond 
			((null? val) 11) ; The address of the NIL object
			((boolean? val) (if val 14 12)) ; The address of #t\#f objects
			((equal? val (cadar lst)) (caddar lst)) 
			(else (get-address (cdr lst) val)) ; Recursive call		
	)))


; scmFile->list(file)
; Takes .scm file name(as a string) and return list of its sexpr
;
; Type: [String -> List(Sexpr)]
; Example: if "test.scm" contains two lines: Line 1. '(define ..), Line 2. '(lambda ..)
;		   then, (scmFile-list "test.scm") ==> '('(define...) '(lambda...))

(define scmFile->list
	(lambda (file)
    	(let ((in (open-input-file file)))
      	(letrec ((do
			(lambda ()
		  	(let ((sexpr (read in)))
		    	(if (eof-object? sexpr) '()
				(cons sexpr (do)))))))
		(let ((lst (do)))
	  	(close-input-port in)
	  	lst)))
	))

; topological-sort(exp) procedure.
; Takes an expression and sort its sub-expressions before the root expression.
; For symbols, we create a string representation and put it before the symbol itself.
;
; Type: [T -> Sexpr]
; Example: (topological-sort x) ==> '("x" x)
; NOTE: This procedure presented in Mayer's class.

(define topological-sort
	(lambda (e)

		(cond 
			((pair? e)
				`(,@(topological-sort (car e)) ,@(topological-sort (cdr e)) ,e))
			((symbol? e)
				`(,(symbol->string e) ,e))
			((vector? e)
				`(,@(apply append (map topological-sort (vector->list e))) ,e))
			(else `(,e))
		)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;; Code Generators ;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The main procedure-code generator

(define code-gen
	(lambda (pe env pvars-len)
		(cond
			((tagged-by? 'const pe) (code-gen-const (cadr pe)))
			((tagged-by? 'pvar pe) (code-gen-pvar (cadr pe) (caddr pe))) ; pe=('pvar x minor)
			((tagged-by? 'bvar pe) (code-gen-bvar (cadr pe) (caddr pe) (cadddr pe))); pe=('bvar x major minor)
			((tagged-by? 'fvar pe) (code-gen-fvar (cadr pe))) ; pe=('fvar x)
			((tagged-by? 'if3 pe) (code-gen-if3 (cdr pe) env pvars-len unique-tag))
			((tagged-by? 'or pe) (code-gen-or (cadr pe) env pvars-len unique-tag))
			((tagged-by? 'lambda-simple pe) (code-gen-lambda-simple pe env pvars-len unique-tag))
			((tagged-by? 'lambda-opt pe) (code-gen-lambda-opt pe env pvars-len unique-tag))
			((tagged-by? 'lambda-variadic pe) (code-gen-lambda-variadic pe env pvars-len unique-tag))
			((tagged-by? 'define pe) (code-gen-define (cdr pe) env pvars-len))
			((tagged-by? 'seq pe) (code-gen-seq (cadr pe) env pvars-len unique-tag))
			((tagged-by? 'applic pe) (code-gen-applic pe env pvars-len unique-tag))
			((tagged-by? 'tc-applic pe) (code-gen-tc-applic pe env pvars-len unique-tag))
			(else "")

			);end-of-cond

		))

; Code-Generator for 'const'
; Examples: see tests.

(define code-gen-const
	(lambda(const)
		(string-append "\t/* CONST_ */\n"
			(cond
				((equal? *void-object* const) "\tMOV(R0, IMM(10));\n") ; VOID-Object initialized to be in address 10
				((null? const) "\tMOV(R0, IMM(11));\n") ; NILL-Object initialized to be in address 11
				((and (boolean? const) (equal? #t const)) "\tMOV(R0, IMM(14));\n") ; TRUE-Object initialized to be in address 14
				((and (boolean? const) (equal? #f const)) "\tMOV(R0, IMM(12));\n") ; FALSE-Object initialized to be in address 12
				; Else, It's symbol/number/char/vector/pair
				((or (vector? const) (char? const) (number? const) (symbol? const) (string? const) (pair? const))
				 (string-append "\tMOV(R0,IMM(" (number->string (get-address consts-struct-list const)) "));\n"))))
		))

; Code-Generator for 'pvar'
; The indexes of the minors starting from 0,
; therefore, if we want to make use in the macro-expansion 'FPARG', 
; we need to add 2 to the pvar's minor value.
;
; Examples: see tests.

(define code-gen-pvar
	(lambda(pvar minor)
		(let (
			(str-pvar (symbol->string pvar))
			(addr (number->string (+ 2 minor)))) 
		; Body-of-let
			(string-append "\t/* CG_PVAR_" str-pvar " */\n"
						   "\tMOV(R0,FPARG(" addr "));\n") 
		)))

; Code-Generator for 'bvar'
; Examples: see tests.

(define code-gen-bvar
	(lambda(bvar major minor)

		(let (
			(str-bvar (symbol->string bvar))
			(str-major (number->string major))
			(str-minor (number->string minor)))
		; Body-of-let
			(string-append "\t/* CG_BVAR_" str-bvar " */\n"
						   "\tMOV(R0,FPARG(0));\n" ; R0=env
						   "\tMOV(R0,INDD(R0," str-major "));\n"
						   "\tMOV(R0,INDD(R0," str-minor "));\n")
		)))

; Code-Generator for 'fvar'
; Examples: see tests.

(define code-gen-fvar
	(lambda(fvar)
		(let (
			(str-fvar (symbol->string fvar))
			(symbol-address (number->string (get-address consts-struct-list fvar))) ; The address of the corresponding bucket(of the symbol object)
			(string-address (number->string (get-address consts-struct-list str-fvar)))) ; The address of the corresponding bucket(of the string object)
		; Body-of-let
				(string-append
					"\t/* CG_FVAR_" str-fvar " */\n"
					"\tMOV(R0," symbol-address ");\n"
					"\tMOV(R0,INDD(R0,1));\n" ; Set R0 to point to the bucket in the SYMBOL TABLE
					"\tMOV(R0,INDD(R0,2));\n" ; Set R0 to point to the constant corresponding bucket
					"\tCMP(R0,IMM(0));\n"
					"\tJUMP_EQ(ERROR_UNDEFINED_VAR_H);\n"
					"\tJUMP(NO_ERROR_UNDEFINED);\n"
					"\tERROR_UNDEFINED_VAR_H:\n"
					"\tMOV(R1," string-address ");\n"
					"\tJUMP(ERROR_UNDEFINED_VAR);\n" ; Jump to the LABEL we've already created by 'error' global variable
					"\tNO_ERROR_UNDEFINED:\n"
		)

		)))

; Code-Generator for 'if3'
; Examples: see tests.

(define code-gen-if3
	(lambda(if-lst env pvars-len u-tag)
		(let (
			(str-u-tag (number->string u-tag))
			(test (car if-lst))
			(dit (cadr if-lst))
			(dif (caddr if-lst)))
		; Body-of-let
			(begin (inc-unique-tag) ; Increment global unique-tag
				(string-append
					"\t/* IF_TEST_UNIQUE_TAG_" str-u-tag " */\n"
					(code-gen test env pvars-len)
					"\tCMP(INDD(R0,1),IMM(0));\n"
					"\tJUMP_EQ(DIF_LABEL_UNIQUE_TAG_" str-u-tag ");\n" ; If it's #f object
					"\t/* Then_" str-u-tag " */\n"
					(code-gen dit env pvars-len)
					"\tJUMP(END_OF_IF_UNIQUE_TAG_" str-u-tag ");\n"
					"\tDIF_LABEL_UNIQUE_TAG_" str-u-tag ":\n"
 					"\t/* ELSE_" str-u-tag " */\n"
					(code-gen dif env pvars-len)
					"\tEND_OF_IF_UNIQUE_TAG_" str-u-tag ":\n"
					"")))
		))

; Code-Generator for 'or'
; Examples: see tests.

(define code-gen-or
	(lambda (or-lst env pvars-len u-tag)
		(let ((str-u-tag (number->string u-tag)))
			(begin (inc-unique-tag) ; Increment unique-tag
				(string-append
					"\t/* START_OR_UNIQUE_TAG_" str-u-tag " */\n"
					(apply string-append (map (lambda (e) (string-append 
					"\t/* or_" str-u-tag " | Test expression i */\n"	
					(code-gen e env pvars-len) 
					"\tCMP(INDD(R0,1),IMM(0));\n"
					"\tJUMP_NE(END_OR_" str-u-tag ");\n"
										)) or-lst))
					"\t/* END_OR_UNIQUE_TAG_" str-u-tag " */\n"
			)))				
		))


(define code-gen-part-A-lambda
	(lambda (pe env pvars-len u-tag)
		(let (
			(str-u-tag (number->string u-tag))
			(str-old-env (number->string env))
			(str-new-env (number->string (add1 env)))
			(str-pvars-len (number->string pvars-len)))

			; Generate assembly code of Part A of the closure structure.
			; The structure form is as follows:
			; cell #1: Type(T_CLOSURE), cell #2: a pointer to the new environment,
			; cell #3: a pointer to the CODE of the procedure(aka PART B).
			(string-append
					"\t/* CLOSURE_PART_A - " str-u-tag "*/\n"
					"\tPUSH(R1);\n" ; Stores registers
					"\tPUSH(R2);\n"
					"\tPUSH(R3);\n"
					"\tPUSH(R4);\n"
					"\tPUSH(R5);\n"	
					"\tPUSH(IMM(3));\n"
					"\tCALL(MALLOC);\n" ; Allocate memory for the closure structure
					"\tDROP(IMM(1));\n"
					"\tMOV(IND(R0),IMM(T_CLOSURE));\n"
					"\tMOV(R1,R0);\n" 
					"\tPUSH(IMM(" str-new-env "));\n"
					"\tCALL(MALLOC);\n" ; Allocate memory for new-environment
					"\tDROP(IMM(1));\n"
					"\tMOV(INDD(R1,1),R0);\n" ; Cell #2 points to the new allocated memory
					"\tMOV(R2,IMM(0));\n" ; Initialize values for the loop iterations
					"\tMOV(R3,IMM(1));\n" 
					"LOOP_" str-u-tag ":\n" ; This loop creates the new-environment(the old one+pvars)
					"\tCMP(R2,IMM(" str-old-env "));\n"
					"\tJUMP_GE(END_OF_LOOP_" str-u-tag ");\n"
					"\tMOV(R4,FPARG(0));\n"
					"\tMOV(INDD(R0,R3),INDD(R4,R2));\n"
					"\tADD(R2,IMM(1));\n"
					"\tADD(R3,IMM(1));\n"
					"\tJUMP(LOOP_" str-u-tag ");\n"
					"END_OF_LOOP_" str-u-tag ":\n"
					"\tMOV(R2,R0);\n"
					"\tPUSH(" str-pvars-len ");\n"
					"\tCALL(MALLOC);\n"
					"\tDROP(IMM(1));\n"
					"\tMOV(IND(R2),R0);\n"
					"\tMOV(R4,IMM(0));\n"
					"\tMOV(R5,IMM(2));\n"
					"LOOP_PVARS_" str-u-tag ":\n"
					"\tCMP(R4," str-pvars-len ");\n"
					"\tJUMP_GE(END_LOOP_PVARS_" str-u-tag ");\n"
					"\tMOV(INDD(R0,R4),FPARG(R5));\n"
					"\tADD(R5,IMM(1));\n"
					"\tADD(R4,IMM(1));\n"
					"\tJUMP(LOOP_PVARS_" str-u-tag ");\n"
					"END_LOOP_PVARS_" str-u-tag ":\n"
					"\tMOV(INDD(R1,2),LABEL(L_CLOS_CODE_" str-u-tag "));\n"
					"\tMOV(R0,R1);\n"
					"\tPOP(R5);\n" ; Restore registers
					"\tPOP(R4);\n"
					"\tPOP(R3);\n"
					"\tPOP(R2);\n"
					"\tPOP(R1);\n"
					"\tJUMP(L_CLOS_EXIT_" str-u-tag ");\n"
			))))

; Code-Generator for 'lambda-simple'
; Examples: see tests.

(define code-gen-lambda-simple
	(lambda(pe env pvars-len u-tag)
		(let (
			(str-u-tag (number->string u-tag))
			(lambda-body (caddr pe))
			(lambda-params (cadr pe)))
				(begin (inc-unique-tag)
				(string-append (code-gen-part-A-lambda (cdr pe) env pvars-len u-tag)
					"\t/* CLOSURE_SIMPLE_PART_B _ " str-u-tag "*/\n"
					"L_CLOS_CODE_" str-u-tag ":\n"
					"\tPUSH(FP);\n"
					"\tMOV(FP,SP);\n"
					(code-gen lambda-body (add1 env) (length lambda-params))
					"\tPOP(FP);\n"
					"RETURN;\n"
					"L_CLOS_EXIT_" str-u-tag ":\n"))
		)))

; Code-Generator for 'lambda-opt'
; Examples: see tests.

(define code-gen-lambda-opt
	(lambda(pe env pvars-len u-tag)
		(begin (inc-unique-tag)
			(let (
				(str-u-tag (number->string u-tag))
				(lambda-body (caddr pe))
				(lambda-params (cadr pe))
				(rest-minor (number->string (+ 2 (length (cadr pe)))))) ; params='(x1 x2 ... xn . rest)

				(string-append
					(code-gen-part-A-lambda (cdr pe) env pvars-len u-tag)
					"\t/* CLOSURE_OPT_PART_B _ " str-u-tag "*/\n"
					"L_CLOS_CODE_" str-u-tag ":\n" ; LABEL
					"\tPUSH(FP);\n"
					"\tMOV(FP,SP);\n"
					"\tPUSH(R7);\n"	
					"\t/* For each FPARG(i) generate a list */\n"
					"\tMOV(R7,FPARG(1));\n"
					"\tCMP(R7,IMM(" (number->string (length lambda-params)) "));\n" ; Magic
					"\tJUMP_EQ(OPT_MAGIC_" str-u-tag ");\n"			
					"\tADD(R7,IMM(1));\n"
					"\tPUSH(IMM(11));\n"
					"\tPUSH(FPARG(R7));\n"
					"\tCALL(MAKE_SOB_PAIR);\n"
					"\tDROP(IMM(2));\n"
					"\tSUB(R7,IMM(1));\n"
					"LOOP_OPT_" str-u-tag ":\n" ; LABEL
					"\tCMP(R7,IMM(" rest-minor "));\n"	
					"\tJUMP_LT(END_LOOP_OPT_" str-u-tag ");\n"
					"\tPUSH(R0);\n"
					"\tPUSH(FPARG(R7));\n"
					"\tCALL(MAKE_SOB_PAIR);\n"
					"\tDROP(IMM(2));\n"
					"\tSUB(R7,IMM(1));\n"
					"\tJUMP(LOOP_OPT_" str-u-tag ");\n"
					"\tEND_LOOP_OPT_" str-u-tag ":\n"
					"\tMOV(FPARG(" rest-minor "),R0);\n"
					"OPT_MAGIC_" str-u-tag ":\n" ; LABEL
					"\tPOP(R7);\n"
					"\t/* CLOSURE_OPT_BODY_CREATION */\n"
					(code-gen lambda-body (add1 env) (add1 (length lambda-params)))
					"\tPOP(FP);\n"
					"\tRETURN;\n"
					"L_CLOS_EXIT_" str-u-tag ":\n")
		))))

; Code-Generator for 'lambda-variadic'
; Examples: see tests.

(define code-gen-lambda-variadic
	(lambda (pe env pvars-len u-tag)
	    (begin (inc-unique-tag)
			(let 
				((str-u-tag (number->string u-tag))
				(lambda-body (cadr pe)))
				(string-append
					(code-gen-part-A-lambda pe env pvars-len u-tag)
					"\t/* Part B : lambda-variadic " str-u-tag "*/\n"
					"L_CLOS_CODE_" str-u-tag ":\n"
					"\tPUSH(FP);\n"
					"\tMOV(FP,SP);\n"
					"\tPUSH(R8);\n"	;;;; *** ;;;
					"\t/* stack adjustment for lambda-variadic : make a list (based on pairs) */\n"
					"\tMOV(R8,FPARG(1));\n"
					;;;;;;; MAGIC addition
					"\tCMP(R8,IMM(0));\n"
					"\tJUMP_EQ(PARAMS_VARIADIC_MAGIC_" str-u-tag ");\n"
					;;;;;;;;
					"\tADD(R8,IMM(1));\n"
					"\tPUSH(IMM(11));\n"
					"\tPUSH(FPARG(R8));\n"
					"\tCALL(MAKE_SOB_PAIR);\n"
					"\tDROP(IMM(2));\n"
					"\tSUB(R8,IMM(1));\n"
					;loop - make list of T_PAIR
					"LOOP_PARAMS_VARIADIC_" str-u-tag ":\n"
					"\tCMP(R8,IMM(2));\n"	
					"\tJUMP_LT(END_LOOP_PARAMS_VARIADIC_" str-u-tag ");\n"
					"\tPUSH(R0);\n"
					"\tPUSH(FPARG(R8));\n"
					"\tCALL(MAKE_SOB_PAIR);\n"
					"\tDROP(IMM(2));\n"
					"\tSUB(R8,IMM(1));\n"
					"\tJUMP(LOOP_PARAMS_VARIADIC_" str-u-tag ");\n"
					"\tEND_LOOP_PARAMS_VARIADIC_" str-u-tag ":\n"
					"\tMOV(FPARG(2),R0);\n"
					"PARAMS_VARIADIC_MAGIC_" str-u-tag ":\n"
					"\t/* lambda-variadic body */\n"
					"\tPOP(R8);\n"	;;;; *** ;;;
					(code-gen lambda-body (+ env 1) 1)
					"\tPOP(FP);\n"
					"\tRETURN;\n"
					"L_CLOS_EXIT_" str-u-tag ":\n"
		)))))

; Code-Generator for 'define'.
; Update the third cell of the corresponding bucket in the SYMBOL TABLE.
; Explenation by example:
; let pe=(define (var x) (const 3)).
; Then, (code-gen-define (cdr pe) ..) update the third cell
; of the bucket in the symbol table that the symbol object that points to him is
; the symbol object of x.
;
; Examples: see tests.

(define code-gen-define
	(lambda(def env pvars-len)
		(let ( ; def={FOR EXAMPLE}=((var x) (const 3))
			(parsed-val (cadr def))
			(var (cadar def)) ; Type.var=symbol
			(sym-address (number->string (get-address consts-struct-list (cadar def))))) 
		; Body-of-let
		(string-append
			(code-gen parsed-val env pvars-len)
			"\tMOV(R1," sym-address ");\n"
			"\tMOV(R1,INDD(R1,1));\n" ; R1 Points to the bucket in the SYMBOL TABLE
			"\tMOV(INDD(R1,2),R0);\n" ; Update value
			"\tMOV(R0,IMM(10));\n" ; Return VOID object
			)

		)
		))

; Code-Generator for 'seq'
; Examples: see tests.

(define code-gen-seq
	(lambda(seq-lst env pvars-len u-tag)
		(let ((str-u-tag (number->string u-tag)))
			(begin (inc-unique-tag) ; Increment unique-tag
				(string-append
					"\t/* START_SEQ_UNIQUE_TAG_" str-u-tag " */\n"
					(apply string-append (map (lambda (e) (string-append 
					"\t/* SEQ_" str-u-tag " _ Sequence sub-expression */\n"	
					(code-gen e env pvars-len) 
										)) seq-lst))
					"\t/* END_SEQ_UNIQUE_TAG_" str-u-tag " */\n"
			)))
		))

(define cg-seq
	(lambda (pe env p-length)
		(set-unique-tag)
		(let 
			( (unique-tag (number->string current-unique-tag)) )
			(string-append
				"\t/* BEGIN_SEQ_" unique-tag " */\n"	
				(map-cg-seq-light pe env p-length unique-tag "")
				""))))

(define map-cg-seq-light
	(lambda (pe env p-length unique-tag ans)
		(cond 
			((null? pe) 
				ans)
			((not (list? pe)) 
				(string-append
						ans
						"\t/* seq_" unique-tag " | expression i */\n"	
						(code-gen pe env p-length)
						))
			((list? pe)
				(map-cg-seq-light 
					(cdr pe)
					env
					p-length
					unique-tag
					(string-append
						ans
						"\t/* seq_" unique-tag " | expression i */\n"	
						(code-gen (car pe) env p-length)
						))))))

; Code-Generator for 'applic'
; Examples: see tests.

(define code-gen-applic
	(lambda (pe env pvars-len u-tag)
	    (begin (inc-unique-tag)
			(let 
				((str-u-tag (number->string u-tag))
				(proc (car pe))
				(ops (cadr pe)))
				(string-append
					"\t/* applic_" str-u-tag "*/\n"
					"\tPUSH(R6);\n"	
					"\tPUSH(IMM(11));\n"					; This is for MAGIC 
					(map-code-gen-applic ops env pvars-len str-u-tag 0)
					"\t/* pushing number of operands to stack */\n"
					"\tPUSH(IMM(" (number->string (length ops)) "));\n"
					"\t/* generate applic's operator code */\n"
					(code-gen proc env pvars-len)
					"\t/* final stage of the procedure */\n"
					"\tCMP(IND(R0),IMM(T_CLOSURE));\n"
					"\tJUMP_NE(ERROR_NST);\n"
					"\tPUSH(INDD(R0,1));\n"
					"\tCALLA(INDD(R0,2));\n"
					"\tMOV(R6,STARG(0));\n"
					"\tADD(R6,IMM(3));\n"	; This is for MAGIC 
					"\tDROP(IMM(R6));\n"
					"\tPOP(R6);\n"
					)))))

(define map-code-gen-applic
	(lambda (olst env pvars-len str-u-tag i)
		(if (null? olst)
			""
			(string-append
				(map-code-gen-applic (cdr olst) env pvars-len str-u-tag (add1 i))
				"\t/* applic_" str-u-tag " _ B" (number->string (add1 i)) " */\n"
				(code-gen (car olst) env pvars-len)
				"\tPUSH(R0);\n"
				)
		)))

; Code-Generator for 'tc-applic'
; Examples: see tests.

(define code-gen-tc-applic
	(lambda (pe env pvars-len u-tag)
	    (begin (inc-unique-tag)
			(let
				((str-u-tag (number->string u-tag))
				(proc (car pe))
				(ops (cadr pe)))
				(string-append
					"\t/* tc_applic_" str-u-tag "*/\n"
					(map-code-gen-applic ops env pvars-len str-u-tag 0)
					"\t/* pushing number of operands to stack */\n"
					"\tPUSH(IMM(" (number->string (length ops)) "));\n"
					"\t/* generate tc_applic's operator code */\n"
					(code-gen proc env pvars-len)
					"\t/* And finally..  */\n"
					"\tCMP(INDD(R0,0),IMM(T_CLOSURE));\n"
					"\tJUMP_NE(ERROR_NST);\n"
					"\tPUSH(FPARG(-1));\n"
					"\tMOV(FP,FPARG(-2));\n"
					; copy and run down the old frame
					"\t/********************************************/\n"
				
					"\tJUMPA(INDD(R0,2));\n"
			)))))


(define code-gen-vector-elements
	(lambda (vec i)
		(if (eq? -1 i)
			""
			(string-append
				(code-gen-vector-elements vec (sub1 i))
				"\tPUSH(" (number->string (get-address consts-struct-list (vector-ref vec i))) ");\n"			
				))))	

; code-gen-string->char(s addr) procedure.
; Generates assembly code that push onto the stack, as a string of length 1,
; the chars of the string (push them in last-to-first order).
;
; Type: [String*Number -> String]
; Examples: see tests file

(define code-gen-string->chars
	(lambda (s pos)
		(if (= -1 pos) ""
			; Else
			(string-append (code-gen-string->chars s (sub1 pos))
				"\tPUSH(" (number->string (char->integer (string-ref s pos))) ");\n"			
				))))

; code-gen-primitive-procs(lst) procedure.
; Generates assembly codes that push onto the stack buckets
; for primitive procedures.
;
; Type: [List(T) -> String]
; Examples: see tests file

(define code-gen-primitive-procs
	(lambda (lst)
		(cond
			((null? lst) "")
			((code-gen-label (cadar lst))
				(string-append
					"\t/* lambda for " (code-gen-label (cadar lst)) " */\n"
					"\tPUSH(IMM(3));\n"
					"\tCALL(MALLOC);\n"
					"\tDROP(IMM(1));\n"
					"\tMOV(IND(R0),IMM(T_CLOSURE));\n"
					"\tMOV(INDD(R0,1),IMM(0));\n"
					"\tMOV(INDD(R0,2),LABEL(LABEL_PRIMITIVE_" (code-gen-label (cadar lst)) "));\n"
					"\tMOV(R1," (number->string (get-address consts-struct-list (cadar lst)))  ");\n"
					"\tMOV(R1,INDD(R1,1));\n"
					"\tMOV(INDD(R1,2),R0);\n"
					(code-gen-primitive-procs (cdr lst))))
			(else (code-gen-primitive-procs (cdr lst)))
		)))

(define code-gen-label
	(lambda (proc)
		(cond
			((equal? proc 'bin+) "BIN_PLUS")
			((equal? proc 'bin-) "BIN_MINUS")
			((equal? proc 'procedure?) "IS_PROCEDURE")
			((equal? proc 'vector?) "IS_VECTOR")
			((equal? proc 'symbol?) "IS_SYMBOL")
			((equal? proc 'string?) "IS_STRING")
			((equal? proc 'char?) "IS_CHAR")
			((equal? proc 'number?) "IS_NUMBER")
			((equal? proc 'boolean?) "IS_BOOLEAN")
			((equal? proc 'remainder) "REMAINDER")
			((equal? proc 'bin/) "BIN_DIVIDE")
			((equal? proc 'bin=?) "BIN_IS_EQUAL")
			((equal? proc 'bin<?) "BIN_IS_LESS")
			((equal? proc 'bin*) "BIN_MULTIPLY")
			((equal? proc 'cdr) "CDR")
			((equal? proc 'string->symbol) "STRING_TO_SYMBOL")
			((equal? proc 'eq?) "IS_EQUAL")
			((equal? proc 'set-cdr!) "SET_CDR")
			((equal? proc 'set-car!) "SET_CAR")
			((equal? proc 'apply) "APPLY")
			((equal? proc 'null?) "IS_NULL")
			((equal? proc 'integer->char) "INT_TO_CHAR")
			((equal? proc 'make-string) "MAKE_STRING")
			((equal? proc 'make-vector) "MAKE_VECTOR")
			((equal? proc 'vector-length) "VECTOR_LENGTH")
			((equal? proc 'string-set!) "STRING_SET")
			((equal? proc 'car) "CAR")
			((equal? proc 'string-ref) "STRING_REF" )
			((equal? proc 'vector-set!) "VECTOR_SET")
			((equal? proc 'symbol->string) "SYMBOL_TO_STRING")
			((equal? proc 'char->integer) "CHAR_TO_INT")
			((equal? proc 'string-length) "STRING_LENGTH")
			((equal? proc 'vector-ref) "VECTOR_REF")
			((equal? proc 'pair?) "IS_PAIR")
			((equal? proc 'cons) "CONS")
			(else #f)
			)))

; compile-scheme-file procedure. 
; Writes the assembly code of the sexpr in 'srcFile' to 'targetFile'
;
; Type: [String*String -> Void]
; Args: srcFile-the name of the source file. targetFile-the name of the target file.
; Example: #t

(define compile-scheme-file
	(lambda (srcFile targetFile)
		(let (
			 (target (open-output-file targetFile))
			 ; Convert the src file(and support-code.scm) into a list, and maps the following: parse , pe->lex-pe , annotate-tc
			 (src (map annotate-tc (map pe->lex-pe (map parse (append  
				 (scmFile->list "support-code.scm")
				 (scmFile->list srcFile)))))))
		; Body of let

		; Create global list of constants structures
		(begin (set! consts-struct-list (make-consts-struct-list src))
			(display (string-append
					"	
#include <stdio.h>
#include <stdlib.h>

#define DO_SHOW 1

#include \"arch/cisc.h\"

int main()
{
	START_MACHINE;
	
	JUMP(CONTINUE);

	#include \"arch/char.lib\"
	#include \"arch/io.lib\"
	#include \"arch/math.lib\"
	#include \"arch/string.lib\"
	#include \"arch/system.lib\"
	
	"
	(error)
"
CONTINUE:
	
	/* Initialize stack with default values */
	
	/* Void */
	MOV(ADDR(10), IMM(T_VOID));
	
	/* Nil (Empty List) */
	MOV(ADDR(11), IMM(T_NIL));
	
	/* False (Boolean) */
	MOV(ADDR(12), IMM(T_BOOL));
	MOV(ADDR(13), IMM(0));
	
	/* True (Boolean) */
	MOV(ADDR(14), IMM(T_BOOL));
	MOV(ADDR(15), IMM(1));
	
	/* Increase address */
	ADD(ADDR(0), IMM(15))\n;
	
	/* Here we are generate a sequence of constants buckets in the memory */ 
	"
	(make-const-buckets consts-struct-list)
	
	"/* Update the first free buckets address */"
		
	"MOV(IND(1)," (number->string buckets-first-free-address) ");\n" 

	"/* Here we are generate the symbol table */"
	
	(make-symbol-table (filter (lambda (e) (equal? (car e) 'symbol)) consts-struct-list)
			 buckets-first-free-address) ; For symbol table, we need symbols only
	
	"/* Here we are generate primitive procedures */"
	
	(code-gen-primitive-procs (filter (lambda (e) (equal? (car e) 'symbol)) consts-struct-list)) ; FVARs tagged as symbols

	"/* end of primitive procedures generation */"
	
	"
	/* END of initialization */
	
	/* Fake Env */
	PUSH(IMM(0));
	PUSH(IMM(T_NIL));
	PUSH(LABEL(END));
	PUSH(FP);
	MOV(FP,SP);

	/* code generation */
	"
	(apply string-append (map (lambda(e) (code-gen e 0 0)) src)) ; Maps over the list, and generate proper assembly code
	"
END:
	PUSH(R0);
	CALL(WRITE_SOB);
	DROP(IMM(1));
			
	STOP_MACHINE;

	return 0;
}
")
				target) ;; check write / display
			(close-output-port target)))))


			


		; end-of-let

	


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;; THE END ;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


