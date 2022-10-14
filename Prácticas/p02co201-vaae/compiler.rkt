#lang nanopass

(require nanopass/base)

;; Definición del Lenguaje Fuente
;;Nuevo lenguaje 
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
    pr
    c
    l
    t
    s
    (begin e* ... e)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
     (pr c* ... c)
    (e0 e1 ...)))


;; Definimos un nuevo lenguaje con void y elimininando (if e0 e1)
(define-language LFV
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t))
   (void (v)))
  (Expr (e body)
    x
    pr
    c
    l
    t
    s
    v
    (pr c* ... c)
    (begin e* ... e)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (e0 e1 ...)))

;;Definimos un nuevo lenguaje sin strings como elemento terminal
(define-language LFVS
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (type (t))
   (void (v)))
  (Expr (e body)
    x
    pr
    c
    l
    t
    v
    (pr c* ... c)
    (begin e* ... e)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (e0 e1 ...)))

;; Definición del predicado que verifica las variables

;; Predicado que comprueba que el parámetro recibido sea una variable del lenguaje
(define (variable? x)
  (symbol? x))

;; Predicado que comprueba que el parámetro recibido sea una constante del lenguaje
(define (constant? c)
  (or (boolean? c) (integer? c) (char? c)))

;; Predicado que comprueba que el parámetro recibido sea un primitivo del lenguaje
(define(primitive pr)
  (or (procedure? pr) (equal? pr 'and) (equal? pr 'or)))

;;Predicado que comprueba que el parámetro sea void
(define (void-v? v)
  (void? v))

;; Predicado que comprueba que el parámetro recibido sea un tipo del lenguaje
(define (type? t)
  (or (equal? t 'Bool) (equal? t 'Int) (equal? t 'Char) (equal? t 'List) (equal? t 'String)))


;; Proceso del compilador encargado de hacer explicitas las expresiones
;; begin en el cuerpo de lambda, let y letrec
(define-pass make-explicit : LF (ir) -> LF ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* , t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x*, t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* , t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t*, e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* , t*,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* , t*, e*] ...) (begin ,body* ... ,body))]))

;;Función parser del lenguaje LF
(define-parser parser-LF LF)

;;Función parser del lenguaje LFV
(define-parser parser-LFV LFV)

;;Función parser del lenguaje LFVS
(define-parser parser-LFVS LFVS)
 
;; Ejercicio 2

;;Función que renombra a todas las variables dejandolas unificadas
(define-pass rename-var : LF (ir n) -> LF ()
  (definitions
    ;; Hash table donde guardamos los renombres de las variables deligadas
    (define sustituciones (make-hash))
    ;; Función auxiliar que ya renombra o sustituye cada variable por su nuevo nombre.
    (define (sustituye exp)
      (match exp
        [x (cond
             [(and (variable? x) (hash-has-key? sustituciones x)) (hash-ref! sustituciones x 'non)]
             [(constant? x) x]
             [(type? x) x])]
        [(cons x xs) (cond
                       [(or (primitive? x) (eq? 'begin x) (eq? 'if x)) (cons x(map sustituye xs))]
                       [(or (eq? 'lambda x) (eq? 'let x) (eq? 'letrec x)) (cons x (sustituye (second xs)))])])) 
    ;; Función auxiliar para ir guardando las variables deligadas de los constructores
    (define (guarda-variablesDL exp c)
      (match exp
        ;; Caso en el que ya no hay parámetros o asignaciones, por ahora imprimimos para ver si devuelve lo esperado (se va a cambiar)
        ['() (void)]
        ;; Caso en el que estamos haciendo recursión en una lista de parámetros de una lambda 
        [(cons (list id tipo) lst) (begin
                                     (hash-set! sustituciones id (string->symbol (string-append "x"
                                                                               (number->string c))))
                                     (guarda-variablesDL lst (add1 c)))]
        ;; Caso en el que estamos haciendo recursión en una lista de asignaciones para let y letrec
        [(cons (list id tipo valor) lst) (begin
                                     (hash-set! sustituciones id (string->symbol (string-append "x"
                                                                               (number->string c))))
                                     (guarda-variablesDL lst (add1 c)))]
        ;; Caso en el que recibimos una lambda
        [(list 'lambda (cons (list id tipo) lst) cuerpo) (begin
                                                       (hash-set! sustituciones id (string->symbol (string-append "x"
                                                                                                 (number->string c))))
                                                       (guarda-variablesDL lst (add1 c)))]
        ;; Caso en el que recibimos un let
        [(list 'let (cons (list id tipo valor) lst) cuerpo) (begin
                                                         (hash-set! sustituciones id (string->symbol (string-append "x"
                                                                                                   (number->string c))))
                                                         (guarda-variablesDL lst (add1 c)))]
        ;; Caso en el que recibimos un letrec
        [(list 'letrec (cons (list id tipo valor) lst) cuerpo) (begin
                                                         (hash-set! sustituciones id (string->symbol(string-append "x"
                                                                                                   (number->string c)))))])))
  
    (begin
      (guarda-variablesDL ir n)
      (sustituye ir)))
;; Ejemplos 
;(rename-var '(lambda ((x Int) (y Bool)) (+ 1 2)) 0)
;;(rename-var '(let ((x Int 1) (y Int 2)) x) 0)


;;Ejercicio 3
;;Preproceso del compilador que transforma un if sin else a uno con else
;;Para esto se creó un nuevo lenguaje llamado LFV 
(define-pass remove-one-armed-if : LF (ir) -> LFV ()
  (Expr : Expr (ir) -> Expr()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))

;;(remove-one-armed-if (parser-LF '(if 1 2)))

;;Ejercicio 4
;;Preproceso del compilador que elimina las cadenas como elementos terminales
;;Para esto se creó un nuevo lenguaje llamado LFVS

(define-pass remove-string : LF (ir) -> LFVS ()
  (Expr : Expr (ir) -> Expr()
        [,s (string->list s)]))

;;Ejemplo de como se deben probar las cosas
;(unparse-LFVS(remove-string(parser-LF "Hola")))
;(remove-string(parser-LF 1))
;(remove-one-armed-if (parser-LF '(if 1 2)))
