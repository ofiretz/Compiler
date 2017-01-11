;; support-code for the compiler package

(define map
  ((lambda (y) 
     ((lambda (map1) 
	((lambda (maplist) 
	   (lambda (f . s) 
	     (maplist f s))) 
	 (y (lambda (maplist) 
	      (lambda (f s) 
		(if (null? (car s)) '() 
		    (cons (apply f (map1 car s)) 
			  (maplist f (map1 cdr s))))))))) 
      (y (lambda (map1) 
	   (lambda (f s) 
	     (if (null? s) '() 
		 (cons (f (car s)) 
		       (map1 f (cdr s))))))))) 
   (lambda (f) 
     ((lambda (x) 
	(f (lambda args 
	     (apply (x x) args)))) 
      (lambda (x) 
	(f (lambda args 
	     (apply (x x) args))))))))
		 
(define yn
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

(define =
	(letrec ((loop
				(lambda (a lst)
					(cond 
						((null? lst) #t)
						((not (bin=? a (car lst))) #f)
						(else (loop (car lst) (cdr lst)))
					))
			))
		(lambda (a . args)
			(loop a args))
			))
	  
;;; rename ++ to +

(define +
  (letrec ((loop
	    (lambda (s)
	      (if (null? s)
		  0
		  (bin+ (car s)
			(loop (cdr s)))))))
    (lambda s (loop s))))

;;; opt=


;;; rename ** to *

(define *
  (letrec ((loop
	    (lambda (s)
	      (if (null? s)
		  1
		  (bin* (car s)
			(loop (cdr s)))))))
    (lambda s (loop s))))

;;; rename -- to -

(define -
  (lambda (a . s)
    (if (null? s)
	(bin- 0 a)
	(bin- a (apply + s)))))

;;; rename // to /

(define /
  (lambda (a . s)
    (if (null? s)
	(bin/ 1 a)
	(bin/ a (apply * s)))))

;;;

(define add1 (lambda (n) (bin+ n 1))) 
(define sub1 (lambda (n) (bin- n 1)))

(define order
  (lambda (<)
    (letrec ((loop
	      (lambda (a s)
		(or (null? s)
		    (and (< a (car s))
			 (loop (car s) (cdr s)))))))
      (lambda (a . s)
	(loop a s)))))

;;; extension: a variadic not-equal
(define <>
  (letrec ((loop
	    (lambda (a s)
	      (or (null? s)
		  (and (andmap (lambda (b) (not (= a b))) s)
		       (loop (car s) (cdr s)))))))
    (lambda s
      (loop (car s) (cdr s)))))

(define not (lambda (x) (if x #f #t)))

(define foldr
  (lambda (binop final s)
    (letrec ((loop
	      (lambda (s)
		(if (null? s) final
		    (binop (car s) (loop (cdr s)))))))
      (loop s))))

(define compose
  (let ((binary-compose
	 (lambda (f g)
	   (lambda (x)
	     (f (g x))))))
    (lambda s
      (foldr binary-compose (lambda (x) x) s))))

(define caar (compose car car))
(define cadr (compose car cdr))
(define cdar (compose cdr car))
(define cddr (compose cdr cdr))
(define caaar (compose car caar))
(define caadr (compose car cadr))
(define cadar (compose car cdar))
(define caddr (compose car cddr))
(define cdaar (compose cdr caar))
(define cdadr (compose cdr cadr))
(define cddar (compose cdr cdar))
(define cdddr (compose cdr cddr))
(define caaaar (compose car caaar))
(define caaadr (compose car caadr))
(define caadar (compose car cadar))
(define caaddr (compose car caddr))
(define cadaar (compose car cdaar))
(define cadadr (compose car cdadr))
(define caddar (compose car cddar))
(define cadddr (compose car cdddr))
(define cdaaar (compose cdr caaar))
(define cdaadr (compose cdr caadr))
(define cdadar (compose cdr cadar))
(define cdaddr (compose cdr caddr))
(define cddaar (compose cdr cdaar))
(define cddadr (compose cdr cdadr))
(define cdddar (compose cdr cddar))
(define cddddr (compose cdr cdddr))

(define ^variadic-right-from-binary
  (lambda (binary-op base-value)
    (letrec ((op-list
	      (lambda (s)
		(if (null? s) base-value
		    (binary-op (car s) (op-list (cdr s)))))))
      (lambda args
	(op-list args)))))

(define ^variadic-left-from-binary
  (lambda (binary-op base-value)
    (letrec ((op-list
	      (lambda (acc s)
		(if (null? s) acc
		    (op-list (binary-op acc (car s)) (cdr s))))))
      (lambda args
	(if (null? args) base-value
	    (op-list (car args) (cdr args)))))))

(define ^char-op
  (lambda (int-op)
    (lambda (ch1 ch2)
      (int-op (char->integer ch1) (char->integer ch2)))))

;;; You need to have the following binary boolean predicates:
;;; bin<?
;;; bin=?

(define bin>? (lambda (a b) (bin<? b a)))
(define bin<=? (lambda (a b) (not (bin>? a b))))
(define bin>=? (lambda (a b) (not (bin<? a b))))

(define < (order bin<?))
(define <= (order bin<=?))
(define > (order bin>?))
(define >= (order bin>=?))

(define char=? (order (^char-op bin=?)))
(define char<=? (order (^char-op bin<=?)))
(define char<? (order (^char-op bin<?)))
(define char>=? (order (^char-op bin>=?)))
(define char>? (order (^char-op bin>?)))

(define char-uppercase?
  (lambda (ch)
    (and (char<=? #\A ch)
	 (char<=? ch #\Z))))

(define char-lowercase?
  (lambda (ch)
    (and (char<=? #\a ch)
	 (char<=? ch #\z))))

(define char-upcase
  (let ((char-aA (- (char->integer #\a) (char->integer #\A))))
    (lambda (ch)
      (if (char-lowercase? ch)
	  (integer->char
	   (- (char->integer ch) char-aA))
	  ch))))

(define char-downcase
  (let ((char-aA (- (char->integer #\a) (char->integer #\A))))
    (lambda (ch)
      (if (char-uppercase? ch)
	  (integer->char
	   (+ (char->integer ch) char-aA))
	  ch))))

(define char-ci<=?
  (order
   (lambda (ch1 ch2)
     (char<=? (char-upcase ch1) (char-upcase ch2)))))

(define char-ci<?
  (order
   (lambda (ch1 ch2)
     (char<? (char-upcase ch1) (char-upcase ch2)))))

(define char-ci=?
  (order
   (lambda (ch1 ch2)
     (char=? (char-upcase ch1) (char-upcase ch2)))))

(define char-ci>?
  (order
   (lambda (ch1 ch2)
     (char>? (char-upcase ch1) (char-upcase ch2)))))

(define char-ci>=?
  (order
   (lambda (ch1 ch2)
     (char>=? (char-upcase ch1) (char-upcase ch2)))))

(define string-upcase
  (lambda (string)
    (list->string
     (map char-upcase (string->list string)))))

(define string-downcase
  (lambda (string)
    (list->string
     (map char-downcase (string->list string)))))

(define even?
  (lambda (n)
    (zero? (remainder n 2))))

(define odd?
  (lambda (n)
    (not (zero? (remainder n 2)))))

(define length
  (lambda (s)
    (if (null? s) 0
	(add1 (length (cdr s))))))

(define list (lambda args args))

(define list-ref
  (lambda (s i)
    (if (zero? i) (car s)
	(list-ref (cdr s) (- i 1)))))

(define list?
  (lambda (e)
    (or (null? e)
	(and (pair? e)
	     (list? (cdr e))))))

(define member?
  (lambda (a s)
    (ormap (lambda (b) (eq? a b)) s)))

(define negative? (lambda (n) (< n 0)))

(define positive? (lambda (n) (> n 0)))

(define zero? (lambda (x) (= x 0)))

(define vector (lambda args (list->vector args)))

(define equal?
  (let ((void-object (if #f #f)))
    (letrec ((equal?
	      (lambda (a b)
		(cond
		 ;; bool
		 ((and (boolean? a) (boolean? b))
		  (boolean=? a b))
		 ;; char
		 ((and (char? a) (char? b)) (char=? a b))
		 ;; nil
		 ((null? a) (null? b))
		 ;; number
		 ((and (number? a) (number? b)) (= a b))
		 ;; pair
		 ((and (pair? a) (pair? b))
		  (and (equal? (car a) (car b))
		       (equal? (cdr a) (cdr b))))
		 ;; string
		 ((and (string? a) (string? b)) (string=? a b))
		 ;; symbol
		 ((and (symbol? a) (symbol? b)) (eq? a b))
		 ;; vector
		 ((and (vector? a) (vector? b)
		       (= (vector-length a) (vector-length b)))
		  (equal? (vector->list a) (vector->list b)))
		 ;; void
		 ((eq? a void-object) (eq? b void-object))
		 (else #f)))))
      equal?)))

(define ormap
  (lambda (f . s)
    (letrec ((loop
	      (lambda (s)
		(and (pair? (car s))
		     (or (apply f (map car s))
			 (loop (map cdr s)))))))
      (loop s))))

(define andmap
  (lambda (f . s)
    (letrec ((loop
	      (lambda (s)
		(or (null? (car s))
		    (and (apply f (map car s))
			 (loop (map cdr s)))))))
      (loop s))))

(define string->list
  (letrec ((loop
	    (lambda (str n s)
	      (if (= n -1) s
		  (loop str
			(- n 1)
			(cons (string-ref str n) s))))))
    (lambda (str)
      (loop str (- (string-length str) 1) '()))))

(define binary-string=?
  (lambda (str1 str2)
    (let ((n1 (string-length str1))
	  (n2 (string-length str2)))
      (and (= n1 n2)
	   (let ((s1 (string->list str1))
		 (s2 (string->list str2)))
	     (andmap char=? s1 s2))))))

(define binary-string<?
  (lambda (str1 str2)
    (letrec ((loop
	      (lambda (s1 s2)
		(cond ((null? s1) (pair? s2))
		      ((null? s2) #f)
		      ((char=? (car s1) (car s2))
		       (loop (cdr s1) (cdr s2)))
		      (else (char<? (car s1) (car s2)))))))
      (loop (string->list str1)
	    (string->list str2)))))

(define binary-string>? (lambda (str1 str2) (binary-string<? str2 str1)))

(define binary-string<=?
  (lambda (str1 str2) (not (binary-string>? str1 str2))))

(define binary-string>=?
  (lambda (str1 str2) (not (binary-string<? str1 str2))))

(define string=? (order binary-string=?))
(define string<? (order binary-string<?))
(define string>? (order binary-string>?))
(define string<=? (order binary-string<=?))
(define string>=? (order binary-string>=?))

(define vector->list
  (letrec ((loop
	    (lambda (v n s)
	      (if (= n -1) s
		  (loop v
			(- n 1)
			(cons (vector-ref v n) s))))))
    (lambda (v)
      (loop v (- (vector-length v) 1) '()))))

(define list->string
  (lambda (s)
    (let* ((n (length s))
	   (str (make-string n)))
      (letrec ((loop
		(lambda (s i)
		  (if (= i n) str
		      (begin
			(string-set! str i (car s))
			(loop (cdr s) (+ i 1)))))))
	(loop s 0)))))

(define list->vector
  (lambda (s)
    (let* ((n (length s))
	   (v (make-vector n)))
      (letrec ((loop
		(lambda (s i)
		  (if (= i n) v
		      (begin
			(vector-set! v i (car s))
			(loop (cdr s) (+ i 1)))))))
	(loop s 0)))))

(define member
  (lambda (a s)
    (cond ((null? s) #f)
	  ((equal? (car s) a) s)
	  (else (member a (cdr s))))))

;;; this procedure is defined as an abstraction over assoc/assq,
;;; with the potential to define assoc over new and interesting
;;; predicates...
(define ^associate
  (lambda (equal?)
    (letrec ((run
	      (lambda (a s)
		(cond ((null? s) #f)
		      ((equal? (caar s) a) (car s))
		      (else (run a (cdr s)))))))
      run)))

(define assoc (^associate equal?))

(define assq (^associate eq?))

(define boolean=?
  (lambda (a b)
    (if (and (boolean? a) (boolean? b))
	(if a b (not b))
	#f ; should have generated an error message!
	)))

(define void
  (let ((void-object
	 (if #f #f)))
    (lambda () void-object)))

(define void?
  (let ((void-object (void)))
    (lambda (x) (eq? x void-object))))

(define string-append
  (lambda s
    (list->string (apply append (map string->list s)))))

(define vector-append
  (lambda s
    (list->vector (apply append (map vector->list s)))))

(define append
  (letrec ((app2
	    (lambda (s1 s2)
	      (if (null? s1) s2
		  (cons (car s1)
		   (app2 (cdr s1) s2)))))
	   (appl
	    (lambda (s1 s)
	      (if (null? s) s1
		  (app2 s1 (appl (car s) (cdr s)))))))
    (lambda s
      (if (null? s) '()
	  (appl (car s) (cdr s))))))

(define reverse
  (letrec ((loop
	    (lambda (s r)
	      (if (null? s) r
		  (loop (cdr s) (cons (car s) r))))))
    (lambda (s)
      (loop s '()))))

(define string-reverse
  (compose
   list->string
   reverse
   string->list))

(define list-ref
  (lambda (s i)
    (if (zero? i) (car s)
	(list-ref (cdr s) (- i 1)))))

(define list-set!
  (lambda (s i x)
    (if (zero? i) (set-car! s x)
	(list-set! (cdr s) (- i 1) x))))

(define max
  (let ((binary-max (lambda (a b) (if (> a b) a b))))
    (lambda (a . s)
      (foldr binary-max a s))))

(define min
  (let ((binary-min (lambda (a b) (if (< a b) a b))))
    (lambda (a . s)
      (foldr binary-min a s))))

;;; in principle, you need the (error ... ) procedure for this,
;;; but as long as you don't call it everything should be fine.
;;; alternately, you can implement it. :-)

(define format
  (letrec ((st0
	    (lambda (fs args)
	      (cond ((null? fs)
		     (if (null? args)
			 '()
			 (error 'format "Too many arguments" args)))
		    ((char=? (car fs) #\~) (st1 (cdr fs) args))
		    (else (cons (car fs) (st0 (cdr fs) args))))))
	   (st1
	    (lambda (fs args)
	      (cond ((null? fs) (st0 fs args))
		    ((char=? (car fs) #\a)
		     (append (string->list
			      (sexpr->display-string
			       (car args)))
			     (st0 (cdr fs) (cdr args))))
		    ((char=? (car fs) #\s)
		     (append (string->list (sexpr->string (car args)))
			     (st0 (cdr fs) (cdr args))))
		    ((char=? (car fs) #\%)
		     (cons #\newline (st0 (cdr fs) args)))
		    ((char=? (car fs) #\~)
		     (cons #\~ (st0 (cdr fs) args)))
		    (else (error 'format
				 "Unrecognized meta-character"
				 (car fs)))))))
    (lambda (format-string . args)
      (list->string (st0 (string->list format-string) args)))))

(define sexpr->string
  (letrec ((run
	    (lambda (e)
	      (cond ((null? e) "()")
		    ((boolean? e) (if e "#t" "#f"))
		    ((char? e) (char->string e))
		    ((number? e) (number->string e))
		    ((symbol? e) (symbol->string e))
		    ((pair? e)
		     (string-append "(" (pair->string (car e) (cdr e)) ")"))
		    ((string? e) (string->string e))
		    ((vector? e) (vector->string e))
		    ((void? e) "#<void>")
		    ((procedure? e) "#<procedure>")
		    (else (error 'sexpr->string "What's this" e)))))
	   (vector->string
	    (lambda (v)
	      (let ((n (vector-length v))
		    (s (vector->list v)))
		(string-append
		 "#"
		 (run n)
		 (run s)))))
	   (string->string
	    (letrec ((st0
		      (lambda (s)
			(cond ((null? s) '())
			      ((char=? (car s) #\newline)
			       (append '(#\\ #\n)
				       (st0 (cdr s))))
			      ((char=? (car s) #\return)
			       (append '(#\\ #\r)
				       (st0 (cdr s))))
			      ((char=? (car s) #\\)
			       (append '(#\\ #\\)
				       (st0 (cdr s))))
			      ((char=? (car s) #\")
			       (append '(#\\ #\")
				       (st0 (cdr s))))
			      ((char<? (car s) #\space)
			       (append '(#\\)
				       (octal-chars (char->integer (car s)))
				       (st0 (cdr s))))
			      (else (cons (car s) (st0 (cdr s))))))))
	      (lambda (string)
		(list->string
		 (append '(#\")
			 (st0 (string->list string))
			 '(#\"))))))
	   (octal-chars
		      (lambda (m)
			(let* ((o3 (digit (remainder m 8)))
			       (n (quotient m 8))
			       (o2 (digit (remainder n 8)))
			       (n (quotient n 8))
			       (o1 (digit (remainder n 8)))
			       (n (quotient n 8)))
			  (if (zero? n)
			      (list o1 o2 o3)
			      (error 'octal-chars "Not an octal char" m)))))
	   (digit
	    (let ((ascii0 (char->integer #\0)))
	      (lambda (n)
		(integer->char (+ ascii0 n)))))
	   (pair->string
	    (lambda (a d)
	      (let ((string-a (run a)))
		(cond ((null? d) string-a)
		      ((pair? d)
		       (let ((string-d (pair->string (car d) (cdr d))))
			 (string-append string-a " " string-d)))
		      (else (let ((string-d (run d)))
			      (string-append string-a " . " string-d)))))))
	   (char->string
	    (lambda (ch)
	      (cond ((char=? ch #\newline) "#\\newline")
		    ((char=? ch #\space) "#\\space")
		    ((char=? ch #\tab) "#\\tab")
		    ((char=? ch #\return) "#\\return")
		    ((char<? ch #\space)
		     (list->string
		      (append '(#\# #\\)
			      (octal-chars (char->integer ch)))))
		    (else (list->string
			   (list #\# #\\ ch)))))))
    (lambda (e)
      (if (void? e)
	  ""
	  (run e)))))

(define sexpr->display-string
  (letrec ((run
	    (lambda (e)
	      (cond ((null? e) "()")
		    ((boolean? e) (if e "#t" "#f"))
		    ((char? e) (char->string e))
		    ((number? e) (number->string e))
		    ((symbol? e) (symbol->string e))
		    ((pair? e)
		     (string-append "(" (pair->string (car e) (cdr e)) ")"))
		    ((string? e) e)
		    ((vector? e) (vector->string e))
		    ((void? e) "#<void>")
		    ((procedure? e) "#<procedure>")
		    (else (error 'sexpr->string "What's this" e)))))
	   (vector->string
	    (lambda (v)
	      (let ((n (vector-length v))
		    (s (vector->list v)))
		(string-append
		 "#"
		 (run n)
		 (run s)))))
	   (pair->string
	    (lambda (a d)
	      (let ((string-a (run a)))
		(cond ((null? d) string-a)
		      ((pair? d)
		       (let ((string-d (pair->string (car d) (cdr d))))
			 (string-append string-a " " string-d)))
		      (else (let ((string-d (run d)))
			      (string-append string-a " . " string-d)))))))
	   (char->string
	    (lambda (ch)
	      (list->string
	       (list ch)))))
    (lambda (e)
      (if (void? e)
	  ""
	  (run e)))))
