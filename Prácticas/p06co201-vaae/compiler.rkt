#lang nanopass
(require racket/hash)
(define count 0)

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr)))

(define (primitiva? x) (memq x '(+ - * / length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

;; SISTEMA DE TIPOS
;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
(define (c-type? x) (if (list? x) 
	(let* (
		[f (car x)]
		[s (cadr x)]
		[t (caddr x)])
	(or (and (equal? f 'List) (equal? s 'of) (type? t)) 
		(and (type? f) (equal? s '→) (type? t))))
	#f))

(define (arit? x) (memq x '(+ - * /)))

(define (lst? x) (memq x '(length car cdr)))
;Lenguaje Fuente
(define-language LF
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t)))
  (Expr (e body)
    x
    c
    l
    s
    pr
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* ...)
    (e0 e1 ...)))
;Lenguaje en el que se sustituye las multiples expresiones en el cuerpo de
;lambda, let y letrec por una única expresión begin
(define-language L0
  (extends LF)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body* ... body)
           (let ([x* t* e*] ...) body* ... body)
           (letrec ([x* t* e*] ...) body* ... body))
        (+ (lambda ([x* t*] ...) body)
           (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))))

;; Definimos un nuevo lenguaje con void y elimininando (if e0 e1)
(define-language LFV
  (extends L0)
  (Expr (e body)
        (- (if e0 e1))))

;;Definimos un nuevo lenguaje sin strings como elemento terminal
(define-language L3
  (extends L0)
  (terminals
  (- (string (s))))
  (Expr (e body)
        (- s)))

;; Definición del nuevo lenguaje L4
(define-language L4
  (extends L3)
  (terminals
   (- (primitive (pr)))
   (+ (primitiva (pr))))
   (Expr (e body)
         (- pr)
         (+ pr)))

;;Definimos un nuevo lenguaje con operadores lógicos como expresiones
(define-language LIF
  (extends L4)
  (Expr (e body)
        (+ (and e0 e1)
           (or e0 e1)
           (not e))))

;; Definimos un nuevo lenguaje en donde agregamos el constructor primapp
(define-language L5
  (extends L4)
  (Expr (e body)
        (+ (primapp pr e* ...))))


;;Definimos un nuevo lenguaje en donde se agregará el quote y se eliminarán las constantes
(define-language L6
  (extends L5)
  (Expr (e body)
        (+ (cuote c))))

;; Definimos un nuevo lenguaje en donde el let y letrec sólo reciban un parámetro
(define-language L7
  (extends L6)
  (Expr (e body)
        (- (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))
        (+ (let ([x t e]) body)
           (let () body)
           (letrec ([x t e]) body)
           (letrec () body))))

;; Definimos un nuevo lenguaje en donde hay un nuevo constructor letfun
(define-language L8
  (extends L7)
  (Expr (e body)
        (+ (letfun ([x t e]) body))))

;; Definimos un nuevo lenguaje en donde las lambdas sólo reciben un parámetro y la aplicación de simplifica
(define-language L9
  (extends L8)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body)
           (e0 e1 ...))
        (+ (lambda ([x t]) body)
           (e0 e1))))

;; Definimos un nuevo lenguaje en donde agregamos el constructor const para agregar el tipo a las constantes.
(define-language L10
  (extends L9)
  (Expr (e body)
        (- (cuote c))
        (+ (const t c))))

;; Definimos un nuevo lenguaje donde las lambdas vuelven a estar descurrificadas
(define-language L11
  (extends L10)
  (Expr (e body)
        (- (lambda ([x t]) body))
        (+ (lambda ([x* t*] ...) body* ... body))))

;: Definimos un nuevo lenguaje donde let, letrec y letfun ahora sólo reciben una variable
(define-language L12
  (extends L11)
  (Expr (e body)
        (- (let ([x t e]) body)
           (letrec ([x t e]) body)
           (letfun ([x t e]) body))
        (+ (let e)
           (letrec e)
           (letfun e))))

;; PARSERS
(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-LFV LFV)
(define-parser parser-L3 L3)
(define-parser parser-LIF LIF)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L12 L12)

;; Práctica 6
;; Ejercicio 1
;; Proceso que se encarga de descurrificar las expresiones lambda
(define-pass uncurry : L10(ir) -> L11()
  (definitions
    (define (descurrifica expr lst)
      (nanopass-case (L10 Expr) expr                    
                     [(lambda ([,x ,t]) ,body)
                        (let* ([var x]
                               [tipo t]
                               [params (cons (cons var (cons tipo empty)) empty)])
                          (descurrifica body (append params lst)))]
                     [else `(lambda ,lst ,(unparse-L10 expr))])))    
  (Expr : Expr(ir) -> Expr()
        [(lambda ([,x ,t]) ,body)  (parser-L11 (descurrifica ir '()))]))

;; Ejercicio 2
;; Función que que genera la tabla de símbolos de una expresión del lenguaje.
(define (symbol-table-var expr table)
  (nanopass-case (L11 Expr) expr
                 [,x table]
                 [(const ,t ,c) table]
                 [(list) table]
                 [(list ,e* ...) (begin
                                   (define t (map (lambda (x) (symbol-table-var  x (make-hash empty))) e*))
                                   (for-each (lambda (x) (hash-union! table x)) t)
                                   table)]
                 [(begin  ,e* ... ,e) (begin
                                        (define t0 (map (lambda (x) (symbol-table-var  x (make-hash empty))) e*))
                                        (for-each (lambda (x) (hash-union! table x)) t0)
                                        (define t (symbol-table-var e (make-hash empty)))
                                        (hash-union! table t)
                                        table)]
                 [(primapp ,pr ,e* ...)(begin
                                         (define t (map (lambda (x) (symbol-table-var  x (make-hash empty))) e*))
                                         (for-each (lambda (x) (hash-union! table x)) t)
                                         table)]
                 [(if ,e0 ,e1 ,e2) (begin
                                     (define t0 (symbol-table-var e0 (make-hash empty)))
                                     (define t1 (symbol-table-var e1 (make-hash empty)))
                                     (define t2 (symbol-table-var e2 (make-hash empty)))
                                     (hash-union! table t0)
                                     (hash-union! table t1)
                                     (hash-union! table t2)
                                     table)]
                 [(lambda ([,x ,t]) ,body) (begin
                                             (define t (symbol-table-var body (make-hash empty)))
                                             (hash-union! table t)
                                             table)]
                 [(let ([,x ,t ,e]) ,body) (begin
                                             (hash-set! table x (cons t (unparse-L11 e)))
                                             (symbol-table-var body table))]
                 [(letrec ([,x ,t ,e]) ,body) (begin
                                                (hash-set! table x (cons t (unparse-L11 e)))
                                                (symbol-table-var body table))]
                 [(letfun ([,x ,t ,e]) ,body) (begin
                                                (hash-set! table x (cons t (unparse-L11 e)))
                                                (symbol-table-var body table))]
                 [(,e0 ,e1) (begin
                            (define t0 (symbol-table-var e0 (make-hash empty)))
                            (define t1 (symbol-table-var e1 (make-hash empty)))
                            (hash-union! table t0)
                            (hash-union! table t1)
                            table)]))

;; Ejercicio 3
;; Función auxiliar que cambia el constructor
(define (change-constructor exp)
  (nanopass-case (L11 Expr) exp
                  [(let ([,x ,t ,e]) ,body) (parser-L12 `(let ,(unparse-L11 body)))]
                  [(letrec ([,x ,t ,e]) ,body) (parser-L12 `(letrec ,(unparse-L11 body)))]
                  [(letfun ([,x ,t ,e]) ,body) (parser-L12 `(letfun ,(unparse-L11 body)))]
                  [else exp]))

;; Proceso que quita a las expresiones let,letrec y letfun las asignaciones y
;; devuelve la expresión con su tabla de símbolos.
(define-pass assigment : L11(ir) -> L12 (ht)
  (values (change-constructor ir) (symbol-table-var ir (make-hash empty))))

