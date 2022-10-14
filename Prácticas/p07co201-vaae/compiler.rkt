#lang nanopass

(define fun-count 0)

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

;; Predicado de len
(define (len? x)
  (integer? x))

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

(define-language L12
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
  (Expr (e body)
    x
    (const t c)
    (begin e* ... e)
    (primapp pr e* ...)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body)
    (let ([x t e]) body)
    (letrec ([x t e]) body)
    (letfun ([x t e]) body)
    (list e* ...)
    (e0 e1 ...)))

;; Definimos un nuevo lenguaje donde agregamos el constructor de array y eliminamos las listas
(define-language L13
  (extends L12)
  (terminals
   (+ (len (len))))
  (Expr (e body)
        (- (list e* ...))
        (+ len
         (array len t [e* ...]))))

;; Parsers
(define-parser parser-L12 L12)
(define-parser parser-L13 L13)

;; Función que verifica si dos tipos son unificables, para mas detalle consultar 
;; la especificación.
(define (unify t1 t2)
  (if (and (type? t1) (type? t2))
    (cond 
      [(equal? t1 t2) #t]
      [(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
      [(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
      [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
      [(and (equal? 'Lambda t1) (list? t2)) (equal? (cadr t2) '→)]
      [(and (equal? 'Lambda t2) (list? t1)) (equal? (cadr t1) '→)]
      [else #f])
    (error "Se esperaban 2 tipos")))

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
  (if (equal? (car lst) 'List)
    (part (cdr lst))
    (car lst)))

;; Implementación del algoritmo J que devuelve un tipo o un error
(define (J expr ctx)
  (nanopass-case (L12 Expr) expr
                 [,x (look-up x ctx)]
                 [(const ,t ,c) t]
                 [(list) 'List]
                 [(begin ,e* ... ,e)
                  (let*
                      ([types (map (λ (x) (J x ctx)) e*)]
                       [t (J e ctx)])
                    t)]
                 [(primapp ,pr ,e* ...)
                  (let*
                      ([t (map (λ (x) (J x ctx)) e*)]
                       [b (map (λ (x) (equal? x 'Int)) t)])
                    (cond
                      [(and (arit? pr) (foldr (λ (x y) (and x y)) #t b))
                       'Int]
                      [(equal? pr 'car) (caddr (car t))]
                      [(equal? pr 'cdr) (car t)]
                      [(equal? pr 'length) 'Int]))]
                 [(if ,e0 ,e1 ,e2)
                  (let*
                      ([condicion (J e0 ctx)]
                       [t1 (J e1 ctx)]
                       [t2 (J e2 ctx)])
                    (if (and (equal? condicion 'Bool) (unify t1 t2))
                        t1
                        (error "Los tipos no son unificables")))]
                 [(list ,e* ...) 
                  (let*
                      ([types (map (lambda (x) (J x ctx)) e*)]
                       [t (part types)]
                       [eqt (map (lambda (x) (unify t x)) types)])
                    (if (foldr (lambda (x y) (and x y)) #t eqt)
                        `(List of ,t)
                        (error "La Lista debe ser homogenea")))]
                 [(letrec ([,x ,t ,e]) ,body)
                  (let*
                      ([new-ctx (set-add  ctx (cons x t))]
                       [t0 (J e new-ctx)]
                       [s (J body new-ctx)])
                    (if (unify t t0)
                        s
                        (error "El tipo no corresponde con el valor")))]
                  [(let ([,x ,t ,e]) ,body)
                   (let*
                       ([new-ctx (set-add  ctx (cons x t))]
                        [t0 (J e ctx)]
                        [s (J body new-ctx)])
                     (if (unify t t0)
                         s
                         (error "El tipo no corresponde con el valor")))]
                 [(lambda ([,x* ,t*] ...) ,body)
                 	(let*
                            ([new-ctx (pares x* t* ctx)]
                             [s (J body new-ctx)])
                           `(,t* → ,s))]
                 [(letfun ([,x ,t ,e]) ,body)
                  (let*
                      ([new-ctx (set-add (cons x t) ctx)]
                       [t0 (J e ctx)]
                       [s (J body new-ctx)])
                    (if (and (unify t t0) (equal? (cadr t) '→))
                        s
                        (error "El tipo no corresponde con el valor")))]
                 [(,e0 ,e1) (let*
                                ([t0 (J e0 ctx)]
                                 [t1 (J e1 ctx)])
                              (if (and (esFuncion? t0) (unify t0 `(,t1 → ,(caddr t0))))
                                  (caddr t0)
                                  (error 'J "El tipo no corresponde con el valor")))]))


;; Función auxiliar que verifica si un tipo corresponde a una función
;; Regresa true si es así y en otro caso false
(define (esFuncion? x)
  (if (list? x)
      (let* ([f (car x)]
             [s (cadr x)]
             [t (caddr x)])
        (and (type? f) (equal? s '→) (type? t)))
	#f))

;; Función auxiliar que busca un par de variable y tipo en el contexto
;; Si no está regresa un error
(define (look-up var ctx)
 	(cond 
 		[(null? ctx) (error "Sin tipo")]
 		[(equal? var (caar ctx))(cdar ctx)]
 		[else (look-up var (cdr ctx))]))

;; Función auxiliar para construir una nueva tabla de símbolos para las lambdas
(define (pares lst1 lst2 tabla)
  (match lst1
    [(list x) (set-add tabla (cons (car lst1) (car lst2)))]
    [(cons x xs) (pares (cdr lst1) (cdr lst2) (set-add tabla (cons (car lst1) (car lst2))))]))

;; Práctica 7
;; Ejercicio 1
;; Proceso encargado de traducir las listas de nuestro lenguaje en arreglos.
(define-pass list-to-array : L12 (ir) -> L13 ()
  (Expr : Expr(ir) -> Expr()
        [(list ,e* ...) 
          (let* ([lista (map unparse-L12 e*)])
            `(array ,(length lista)  ,(parser-L13 (caddr (J ir empty))) ,(parser-L13 lista)))]))


;; Ejercicio 2
;; Función que se encarga de traducir las expresiones al lenguaje de programación C devolviendo cadenas.
(define (c expr)
  (nanopass-case (L13 Expr) expr
                 [,x  (symbol->string x)]
                 [(const ,t ,c) (cond
                                  [(equal? t 'Int) (number->string c)]
                                  [(equal? t 'Char) (string-append "'" (string c) "'")]
                                  [(and (equal? t 'Bool) (equal? c #t)) "1"]
                                  [(and (equal? t 'Bool) (equal? c #f)) "0"]
                                  [else "No es constante"])]
                 [(primapp ,pr ,e* ...) (cond
                                          [(equal? 'car pr) 
                                            (let*
                                                ([arreglo (car (map c e*))]
                                                 [primer_elem (string-append arreglo "\n" "a[0]" "\n")])
                                              (display primer_elem))])]
                 [(array ,len ,t [,e* ...]) (string-append (string-downcase (symbol->string t))
                                                           " a"
                                                           "["
                                                           (number->string len)
                                                           "] ={"
                                                           (list-string (map c  e*))
                                                           "};")]))


;; Función auxiliar que vuelve una lista de elementos a un string
;; separados por comas
(define (list-string tbl)
    (cond 
      [(=(length tbl) 1)   (car tbl)]
      [(null? tbl) ""]
      [(string-append  (car tbl) "," (list-string (cdr tbl)))]))


