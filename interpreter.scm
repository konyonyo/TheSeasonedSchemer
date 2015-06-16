;; utility
(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))

(define add1
  (lambda (x)
    (+ x 1)))

(define sub1
  (lambda (x)
    (- x 1)))

(define name-of
  (lambda (e)
    (car (cdr e))))

(define right-side-of
  (lambda (e)
    (car (cdr (cdr e)))))

(define text-of
  (lambda (e)
    (car (cdr e))))

(define body-of
  (lambda (e)
    (cdr (cdr e))))

(define formals-of
  (lambda (e)
    (car (cdr e))))

(define ccbody-of
  (lambda (e)
    (cdr (cdr e))))

(define else?
  (lambda (e)
    (cond
     [(atom? e) (eq? e 'else)]
     [else #f])))

(define question-of
  (lambda (e)
    (car e)))

(define answer-of
  (lambda (e)
    (car (cdr e))))

(define function-of
  (lambda (e)
    (car e)))

(define arguments-of
  (lambda (e)
    (cdr e)))

(define cond-lines-of
  (lambda (e)
    (cdr e)))
;; utility end

(define abort '())

(define the-empty-table
  (lambda (name)
    (abort (cons 'no-answer (cons name '())))))

(define global-table the-empty-table)

(define extend
  (lambda (name1 value table)
    (lambda (name2)
      (cond
       [(eq? name2 name1) value]
       [else (table name2)]))))

(define a-prim
  (lambda (p)
    (lambda (args-in-a-list)
      (p (car args-in-a-list)))))

(define b-prim
  (lambda (p)
    (lambda (args-in-a-list)
      (p (car args-in-a-list) (car (cdr args-in-a-list))))))

(define *const
  ((lambda (cons car cdr null eq atom zero add1 sub1 number)
     (lambda (e table)
       (cond
	[(number? e) e]
	[(eq? e '#t) #t]
	[(eq? e '#f) #f]
	[(eq? e 'cons) cons]
	[(eq? e 'car) car]
	[(eq? e 'cdr) cdr]
	[(eq? e 'null?) null]
	[(eq? e 'eq?) eq]
	[(eq? e 'atom?) atom]
	[(eq? e 'zero?) zero]
	[(eq? e 'add1) add1]
	[(eq? e 'sub1) sub1]
	[(eq? e 'number?) number])))
   (b-prim cons)
   (a-prim car)
   (a-prim cdr)
   (a-prim null?)
   (b-prim eq?)
   (a-prim atom?)
   (a-prim zero?)
   (a-prim add1)
   (a-prim sub1)
   (a-prim number?)))

(define unbox
  (lambda (box)
    (box (lambda (it set) it))))

(define *identifier
  (lambda (e table)
    (unbox (table e))))

(define atom-to-action
  (lambda (e)
    (cond
     [(number? e) *const]
     [(eq? e '#t) *const]
     [(eq? e '#f) *const]
     [(eq? e 'cons) *const]
     [(eq? e 'car) *const]
     [(eq? e 'cdr) *const]
     [(eq? e 'null?) *const]
     [(eq? e 'eq?) *const]
     [(eq? e 'atom?) *const]
     [(eq? e 'zero?) *const]
     [(eq? e 'add1) *const]
     [(eq? e 'sub1) *const]
     [(eq? e 'number?) *const]
     [else *identifier])))

(define *quote
  (lambda (e table)
    (text-of e)))

(define beglis
  (lambda (es table)
    (cond
     [(null? (cdr es)) (meaning (car es) table)]
     [else ((lambda (val) (beglis (cdr es) table))
	    (meaning (car es) table))])))

(define box
  (lambda (it)
    (lambda (sel)
      (sel it (lambda (new) (set! it new))))))

(define box-all
  (lambda (vals)
    (cond
     [(null? vals) '()]
     [else (cons (box (car vals)) (box-all (cdr vals)))])))

(define multi-extend
  (lambda (names values table)
    (cond
     [(null? names) table]
     [else (extend (car names) (car values)
		   (multi-extend (cdr names) (cdr values) table))])))

(define *lambda
  (lambda (e table)
    (lambda (args)
      (beglis (body-of e)
	      (multi-extend (formals-of e) (box-all args) table)))))

(define *letcc
  (lambda (e table)
    (call/cc
        (lambda (skip)
	   (beglis (ccbody-of e)
		   (extend (name-of e) (box (a-prim skip)) table))))))

(define setbox
  (lambda (box new)
    (box (lambda (it set) (set new)))))

(define *set
  (lambda (e table)
    (setbox (table (name-of e)) (meaning (right-side-of e) table))))

(define list-to-action
  (lambda (e)
    (cond
     [(atom? (car e)) (cond
		       [(eq? (car e) 'quote) *quote]
		       [(eq? (car e) 'lambda) *lambda]
		       [(eq? (car e) 'letcc) *letcc]
		       [(eq? (car e) 'set!) *set]
		       [(eq? (car e) 'cond) *cond]
		       [else *application])]
     [else *application])))

(define expression-to-action
  (lambda (e)
    (cond
     [(atom? e) (atom-to-action e)]
     [else (list-to-action e)])))

(define meaning
  (lambda (e table)
    ((expression-to-action e) e table)))

(define the-meaning
  (lambda (e)
    (meaning e global-table)))

(define define?
  (lambda (e)
    (cond
     [(atom? e) #f]
     [(atom? (car e)) (eq? (car e) 'define)]
     [else #f])))

(define *define
  (lambda (e)
    (set! global-table
	  (extend
	   (name-of e)
	   (box (the-meaning (right-side-of e)))
	   global-table))))

(define value
  (lambda (e)
    (call/cc
        (lambda (the-end)
	   (set! abort the-end)
	   (cond
	    [(define? e) (*define e)]
	    [else (the-meaning e)])))))

(define evcon
  (lambda (lines table)
    (cond
     [(else? (question-of (car lines)))
      (meaning (answer-of (car lines)) table)]
     [(meaning (question-of (car lines)) table)
      (meaning (answer-of (car lines)) table)]
     [else (evcon (cdr lines) table)])))

(define *cond
  (lambda (e table)
    (evcon (cond-lines-of e) table)))

(define evlis
  (lambda (args table)
    (cond
     [(null? args) '()]
     [else ((lambda (val)
	      (cons val (evlis (cdr args) table)))
	    (meaning (car args) table))])))

(define *application
  (lambda (e table)
    ((meaning (function-of e) table) (evlis (arguments-of e) table))))

