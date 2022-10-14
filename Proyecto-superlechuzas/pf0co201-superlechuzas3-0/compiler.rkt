#lang nanopass

(require nanopass/base)
(require racket/set)
(require racket/hash)
(require 2htdp/batch-io)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr and or not equal? < > isZero? ++ --)))

(define (primitiva? x) (memq x '(+ - * / length car cdr < > equal?)))
(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

;;(define (type? x) (memq x '(Bool Char Int List String Lambda)))

;; SISTEMA DE TIPOS
;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
;;Verifica si es un tipo basico
(define (b-type? x) (memq x '(Bool Char Int List String Lambda Void)))
;; Verifica si es un tipo compuesto
(define (c-type? x) (if (list? x) 
  (let* (
    [f (car x)]
    [s (cadr x)]
    [t (caddr x)])
  (or (and (equal? f 'List) (equal? s 'of) (type? t)) 
    (and (type? f) (equal? s '→) (type? t))))
  #f))

;; Verifica si es una primitiva aritmtica
(define (arit? x) (memq x '(+ - * /)))

;; Verifica si es una primitiva de listas
(define (lst? x) (memq x '(length car cdr)))

;; Verifica si es una primitiva que regresa un booleano
(define (arit-bool? x) (memq x '(< > equal?)))

;;funcion encargada de asignar variables unicas
(define make-temp (lambda () (unique-var 't)))

;;funcion encargada de asignar variables unicas
(define make-tempfoo (lambda () (unique-var 'foo)))



;;Crea una variable unica
(define unique-var
  (let()
    (define count 0)
    (lambda (name)
      (let ([c count])
        (set! count (+ count 1))
        (string->symbol
          (string-append (symbol->string name) "."(number->string c)))))))

;; LENGUAJES

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
    (define x e)
    (begin e* ... e)
    (while [e0] e1)
    (for [x e0] e1)
    (if e0 e1)
    (if e0 e1 e2)
    (lambda ([x* t*] ...) body* ... body)
    (let ([x* t* e*] ...) body* ... body)
    (letrec ([x* t* e*] ...) body* ... body)
    (list e* ... )
    (e0 e1 ...)))


(define-language LFOR
	(extends LF)
	(Expr (e body)
		(- (for [x e0] e1))))

;Lenguaje en el que se sustituye las multiples expresiones en el cuerpo de
;lambda, let y letrec por una única expresión begin
(define-language L0
  (extends LFOR)
  (Expr (e body)
        (- (lambda ([x* t*] ...) body* ... body)
           (let ([x* t* e*] ...) body* ... body)
           (letrec ([x* t* e*] ...) body* ... body))
        (+ (lambda ([x* t*] ...) body)
           (let ([x* t* e*] ...) body)
           (letrec ([x* t* e*] ...) body))))


;Lenguaje en el que se unifica if e1 e2 a if e1 e2 e3
(define-language L1
  (extends L0)
  (Expr (e body)
    (- (if e0 e1))))


;; Definición del Lenguaje sin string
(define-language L2
  (extends L1)
  (terminals
    (- (string (s))))
  (Expr (e body)
    (- s)))



;; Definición del nuevo lenguaje L4
(define-language L4
  (extends L2)
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
        (+ (and e* ...)
           (or e* ...)
           (not e* ...)
           (< e* ...)
           (> e* ...)
           (++ e* ...)
           (-- e* ...)
           (isZero? e* ...)
           (equal? e* ...))))


;; Definición del Lenguaje sin string
(define-language L5
  (extends L4)
  (Expr (e body)
        (- pr)
        (+ (primapp pr e* ...))))

;; Definición del Lenguaje sin string

;; Definición del Lenguaje sin string
(define-language Li
  (extends L5)
  (Expr (e body)
     (- c)))

(define-language L6
  (extends Li)
  (Expr (e body)
     (+ (cuote c))))


(define-language L7
  (extends L6)
  (Expr (e body)
     (- (let ([x* t* e*] ...) body)
        (letrec ([x* t* e*] ...) body))
     (+ (let ([x t e] ) body)
        (letrec ([x t e] ) body))))


(define-language L8
  (extends L7)
  (Expr (e body)
     (+ (letfun ([x t e]) body))))


(define-language L9
  (extends L8)
  (Expr (e body)
     (- (lambda ([x* t*] ...) body)
        (e0 e1 ...))
     (+ (lambda ([x t]) body)
        (e0 e1))))

(define-language L10
  (extends L9)
  (Expr (e body)
     (- (cuote c))
     (+ (const t c))))

(define-language L11
  (extends L10)
  (Expr (e body)
        (- (lambda ([x t]) body))
        (+ (lambda ([x* t*] ...) body* ... body))))

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

(define-parser parser-LFOR LFOR)
(define-parser parser-LIF LIF)
(define-parser parser-LF LF)
(define-parser parser-L0 L0)
(define-parser parser-L1 L1)
(define-parser parser-L2 L2)
(define-parser parser-L4 L4)
(define-parser parser-L5 L5)
(define-parser parser-L6 L6)
(define-parser parser-L7 L7)
(define-parser parser-L8 L8)
(define-parser parser-L9 L9)
(define-parser parser-L10 L10)
(define-parser parser-L11 L11)
(define-parser parser-L12 L12)



;; PROCESOS

(define-pass delete-for : LF (ir) -> LFOR ()	
  (Expr : Expr (ir) -> Expr ()
    [(for [,x ,e0] ,e1) 
    	`(while (< (length ,(unparse-LF e0)) 0) ,(unparse-LF e1)) 		
    		 ]
    ))

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `,c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))

;; Proceso del compilador encargado de unificar if con una condicional 
(define-pass remove-one-armed-if : L0 (e) -> L1 ()
  (Expr : Expr (e) -> Expr ()
    [(if ,[e0],[e1])
      `(if ,e0 ,e1 void)]))

;; Proceso del compilador encargado de unificar if con una condicional
(define-pass remove-string : L1 (e) -> L2 ()
  (Expr : Expr (e) -> Expr ()
    [,s (parser-L2 (append '(list)(string->list s)))]))


;; Proceso que cambia del lenguaje L2 a LIF
(define-pass change-language : L2 (ir) -> LIF ()
  (Expr : Expr (ir) -> Expr ()
        [,pr (cond
               [(equal? 'not pr) `(not)]
               [(equal? 'and pr) `(and)]
               [(equal? 'or pr) `(or)]
               [else `,pr])]
        [(,e0 ,[e1] ...) (cond
                        [(and (primitive? e0)(equal? 'not e0)) `(not ,(car e1))]
                        [(and (primitive? e0)(equal? 'and e0)) `(and ,e1 ...)]
                        [(and (primitive? e0)(equal? 'or e0)) `(or ,e1 ...)]
                        [(and (primitive? e0) (equal? '++ e0)) `(+ ,(car e1) 1)]
                        [(and (primitive? e0) (equal? '-- e0)) `(- ,(car e1) 1)]
                        [(and (primitive? e0) (equal? 'isZero? e0)) `(isZero? ,(car e1))]
                        [else `(,e0 ,e1 ...)])]))

;; Proceso que elimina las primitivas and, or y not
(define-pass remove-logical-operators : LIF (ir) -> L4 ()
  (Expr : Expr (ir) -> Expr()
        [(not ,[e]) `(if ,e #f #t)]
        [(or ,[e0] ,[e1]) `(if ,e0 #t ,e1)]
        [(and ,[e0] ,[e1]) `(if ,e0 ,e1 #f)]
        [(isZero? ,[e0]) `(if (equal? ,e0 0) ,#t #f)]))

;; Proceso del compilador encargado de añadir una lambda cada que veamos una pri-
;;mitiva como expresión.
(define-pass eta-expand : L4 (e) -> L5 () ;Agregar ++ --
  (Expr : Expr (e) -> Expr () 
    [(,pr ,[e*] ...) 
      (cond 
        [(memq pr '(+ - * / < > equal?)) 
          (let f ([t1 (make-temp)] [t2 (make-temp)])
          `((lambda ([,t1 ,'Int] [,t2 ,'Int]) (primapp ,pr ,t1 ,t2 ))  ,(car e*) ,(cadr e*)))]
        [(memq pr '(car cdr length)) 
          (let f ([t1 (make-temp)])
          `((lambda ([,t1 ,'List]) (primapp ,pr ,t1 )) ,(car e*) ))])]))

;; Proceso del compilador encargado de quotear constantes.
(define-pass quote-const : L5 (ir) -> L6 ()
    (Expr : Expr (ir) -> Expr ()
      [,c `(cuote ,c)]))

;; Este proceso está encargado de verificar que las expresiones letrec
;; asignen únicamente expresiones lambda a variables.
(define-pass purify-recursion : L6 (ir) -> L6 ()
    (Expr : Expr (ir) -> Expr ()
      [(letrec ([,x* ,t* ,e*] ...) ,[body])
      (let f ([x  x*][t  t*][e  e*])
        (if (null? e)
            body
            (if (equal? (car t) 'Lambda)
                `(letrec ([,(car x) ,(car t) ,(car e)]) ,(f (cdr x)  (cdr t)  (cdr e)) )
                `(let ([,(car x) ,(car t) ,(car e)]) ,(f (cdr x)  (cdr t)  (cdr e)) )
             )))]))


;; Este proceso se encarga de traducir una aplicación de función a una expresión let tomando
;; como nombres de variables los parámetros formales y como valores los parámetros reales.
(define-pass direct-app : L6 (ir) -> L6 ()
    (Expr : Expr (ir) -> Expr ()
      [((lambda ([,x* ,t*] ...) ,[body]) ,[e*] ...)
      `(let ([,x* ,t* ,e*] ...) ,body)]))



;; Este proceso encargado de currificar las expresiones let y letrec.
(define-pass curry-let : L6 (ir) -> L7 ()
    (Expr : Expr (ir) -> Expr ()
      [(letrec ([,x* ,t* ,[e*]] ...) ,[body])
      (let f ([x  x*][t  t*][e  e*])
        (if (null? e)
            body
            `(letrec ([,(car x) ,(car t) ,(car e)]) ,(f (cdr x)  (cdr t)  (cdr e)) )
             ))]
      [(let ([,x* ,t* ,[e*]] ...) ,[body])
      (let f ([x  x*][t  t*][e  e*])
        (if (null? e)
            body
            `(let ([,(car x) ,(car t) ,(car e)]) ,(f (cdr x)  (cdr t)  (cdr e)) )
             ))]))


;; Este proceso  se detecten los let utilizados para definir funciones y se
;; remplazan por letrec.
(define-pass identify-assigments : L7 (ir) -> L7 ()
    (Expr : Expr (ir) -> Expr ()
      [(let ([,x ,t ,[e]]) ,[body])
          (if (equal? t 'Lambda)
            `(letrec ([,x ,t ,e]) ,body)
            ir)]))


;; Este proceso  encargado de asignarle un identificador a las funciones anónimas (lambda).
(define-pass un-anonymous : L7 (ir) -> L8 ()
    (Expr : Expr (ir) -> Expr ()
      [(lambda ([,x* ,t*] ...) ,[body])
            (let ([foo (make-tempfoo)])
              `(letfun ([,foo ,'Lambda (lambda ([,x* ,t*] ...) ,body)]) ,foo ))]))


;;Este proceso funciona como verificador de la sintaxis de las expresiones.
(define-pass verify-arity : L8 (ir) -> L8 ()
  (definitions
    (define (ari? e) (memq e '(+ - * / < > equal?)))
    (define (lst? e) (memq e '(car cdr length))))
    (Expr : Expr (ir) -> Expr ()
      [(primapp ,pr ,[e*] ...)
         (cond
          [ (and (ari? pr) (equal? (length e*) 2)) ir ]
          [ (and (lst? pr) (equal? (length e*) 1)) ir ]
          [ else (error "Arithmetic error")])]))


;;Busca variables libres
(define (FV exp ambiente)
  (nanopass-case (L8 Expr) exp
                 [,x (busca-vars x ambiente)]
                 [(cuote ,c) `()]
                 [(define ,x ,e) (FV e ambiente)]
                 [(begin ,e* ... ,e) (let*
                                         ([envr (actualiza-ar e* ambiente)]
                                          [env  (actualiza-ambiente e envr)])
                                      (set-union (FVR e* ambiente) (FV e env)))]
                 [(while  [,e0] ,e1)  (set-union (FV e1 ambiente) (FV e0 ambiente))]
                 [(primapp ,pr ,e* ...) (FVR e* ambiente)]
                 [(list ,e* ...) (FVR e* ambiente)]
                 [(if ,e0 ,e1 ,e2) (set-union (FV e0 ambiente) (FV e1 ambiente) (FV e2 ambiente))]
                 [(lambda ([,x* ,t*] ...) ,body) (FVR body (append x* ambiente))]
                 [(let ([,x ,t ,e]) ,body) (set-union (FVR body (cons x ambiente)) (FV e ambiente))]
                 [(letrec ([,x ,t ,e]) ,body) (set-union (FVR body (cons x ambiente)) (FV e ambiente))]
                 [(letfun ([,x ,t ,e]) ,body) (set-union (set-remove (FV body ambiente) x) (FV e ambiente))]
                 [(,e0 ,e1 ...)(set-union (FV e0 ambiente) (FVR e1 ambiente))]))

;; Función auxiliar que busca las variables en el ambiente
(define (busca-vars var ambiente)
  (if (empty? ambiente)
      `(,var)
      (if (equal? (car ambiente) var) `()
                     (busca-vars var (cdr ambiente)))))

;; Función auxiliar que actualiza el ambiente dependiendo de la expresión dada
(define (actualiza-ambiente exp ambiente)
  (nanopass-case (L8 Expr) exp
                 [,x ambiente]
                 [(cuote ,c) ambiente]
                 [(define ,x ,e) (cons x ambiente)]
                 [(begin ,e* ... ,e) (actualiza-ambiente e (actualiza-ar e* ambiente))]
                 [(while  [,e0] ,e1)  (actualiza-ambiente e1 (actualiza-ambiente e0 ambiente))]
                 [(primapp ,pr ,e* ...) (actualiza-ar e* ambiente)]
                 [(list ,e* ...)(actualiza-ar e* ambiente)]
                 [(if ,e0 ,e1 ,e2) (actualiza-ambiente e2
                                                       (actualiza-ambiente e1
                                                                           (actualiza-ambiente e0 ambiente)))]
                 [(lambda ([,x* ,t*] ...) ,body) (actualiza-ambiente body (append x* ambiente))]
                 [(let ([,x ,t ,e]) ,body) (actualiza-ambiente body (cons x ambiente))]
                 [(letrec ([,x ,t ,e]) ,body) (actualiza-ambiente body (cons x ambiente))]
                 [(letfun ([,x ,t ,e]) ,body) (actualiza-ambiente body (cons x ambiente))]
                 [(,e0 ,e1 ...)(actualiza-ar e1 (actualiza-ambiente e0 ambiente))]
                 ))

;; Función auxiliar que aplica la función FV de forma recursiva para conservar el ambiente a una lista
(define (FVR lst ambiente)
  (if (= (length lst) 1)
      (FV (car lst)(actualiza-ambiente (car lst) ambiente))
      (let*
          ([nuevo (actualiza-ambiente (car lst) ambiente)])
        (set-union (FV (car lst) ambiente) (FVR (cdr lst) nuevo)))))
                 
;; Función auxiliar que actualiza el ambiente de forma recursiva a una lista
(define (actualiza-ar lst ambiente)
  (if (= (length lst) 1)
      (actualiza-ambiente (car lst) ambiente)
      (let*
          ([nuevo (actualiza-ambiente (car lst) ambiente)])
       (actualiza-ar (cdr lst) nuevo))))


;;El proceso consiste en verificar que la expresión no tenga variables libres, 
;;de existir variables libres se regresa un error en caso contrario la salida es la misma expresión.

(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
      [else (if (empty? (FV ir empty))
              ir
              (error "Free var"))]))

 ;;(verify-vars(parser-L8 '(primapp car (cuote 2)  x)))


 ;; Función que verifica si dos tipos son unificables, para mas detalle consultar 
;; la especificación.
(define (unify t1 t2)
  (if (and (type? t1) (type? t2))
    (cond 
      [(equal? t1 t2) #t]
      [(and (equal? 'List t1) (list? t2)) (equal? (car t2) 'List)]
      [(and (equal? 'List t2) (list? t1)) (equal? (car t1) 'List)]
      [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)) (unify (caddr t1) (caddr t2)))]
      [else #f])
    (error "Se esperaban 2 tipos")))

;; Encuentra el tipo mas particular de una lista de tipos. Para la inferencia de las listas.
(define (part lst)
  (if (equal? (car lst) 'List)
    (part (cdr lst))
    (car lst)))

;;----------------------------Practica 5-----------------------------------

;; Este proceso se encarga de currificar las expresiones lambda así
;;como las aplicaciones de función.
(define-pass curry : L8 (ir) -> L9 ()
    (Expr : Expr (ir) -> Expr ()
      [(lambda ([,x* ,t*] ...) ,[body])
        (let f ([x  x*][t  t*])
       (if (null? t)
            body
            `(lambda ([,(car x) ,(car t)]) ,(f (cdr x) (cdr t)))))]
      [(,e0 ,e1 ...) 
       (let ([me0 (car(reverse e1))] [me1 (append (cdr(reverse e1)) (cons e0 '()))])
       (let f ([a  me0][b me1])
        (if (null? b)
            a
            `(,(f (car b) (cdr b)) ,a ))))]))


;;(curry (parser-L8'(foo x y)))

;;Este proceso se encarga de colocar las anotaciones de tipos
;;correspondientes a las constantes de nuestro lenguaje.
(define-pass type-const : L9 (ir) -> L10 ()
    (Expr : Expr (ir) -> Expr ()
      [(cuote ,c) 
        (cond 
          [(boolean? c) `(const Bool ,c)]
          [(integer? c) `(const Int ,c)]
          [(char? c) `(const Char ,c)])]))
  
;;Función auxiliar se encarga de buscar el tipo de una var en un contexto (lista de pares)
;;Regresa el tipo en otro caso un error de variable libre
(define (look-up var ctx)
  (cond 
    [(null? ctx) (error "Variable libre")]
    [(equal? var (caar ctx)) (cdar ctx)]
    [else (look-up var (cdr ctx))]))

;; Función auxiliar que verifica si un tipo corresponde a una función
;; Mediante en analisis de la lista de tipo (s→t)
(define (funcion? x)
  (if (list? x)
      (let* ([f (car x)]
             [s (cadr x)]
             [t (caddr x)])
        (and (type? f) (equal? s '→) (type? t)))
  #f))


;;Esta función recibe una expresión del lenguaje y un contexto inicial, y regresa el tipo
;;correspondiente a la expresión.
(define (J expr ctx)
  (nanopass-case (L10 Expr) expr
                 [,x (look-up x ctx)]
                 [(const ,t ,c) t]
                 [(define ,x ,e) 
                 	(begin
                 		(set-add  ctx (cons x (J e ctx)))
                 		'Void )]
                 [(list) 'List]
                 [(list ,e* ...) 
                  (let*
                      ([types (map (lambda (x) (J x ctx)) e*)]
                       [t (part types)]
                       [eqt (map (lambda (x) (unify t x)) types)])
                    (if (foldr (lambda (x y) (and x y)) #t eqt)
                        `(List of ,t)
                        (error "La Lista debe ser homogenea")))]
                 [(lambda ([,x ,t]) ,body)
                  (let*
                      ([new-ctx (set-add  ctx (cons x t))]
                      [s (J body new-ctx)])
                    (if (equal? s 'Void) (error "no se puede regresar una asignacion")
                      `(,t → ,s)))]
                 [(let ([,x ,t ,e]) ,body)
                  (let*
                      ([new-ctx (set-add  ctx (cons x t))]
                      [t0 (J e new-ctx)]
                      [s (J body new-ctx)])
                     (if (and (unify t t0) (not (equal? s 'Void)))
                         s
                        (error "El tipo no corresponde con el valor")))]

                 [(if ,e0 ,e1 ,e2)
                  (let*
                      ([condicion (J e0 ctx)]
                       [t1 (J e1 ctx)]
                       [t2 (J e2 ctx)])
                    (if (and (equal? condicion 'Bool) (unify t1 t2) (not (equal? t1 'Void)))
                        t1
                        (error "Los tipos no son unificables")))]
                 [(begin ,e* ... ,e)
                  (let*
                      ([types (map (λ (x) (J x ctx)) e*)]
                       [t (J e ctx)])
                    (if (equal? 'Void t)
                        (error "no se puede regresar una asignacion")
                        t))]
                 [(while [,e0] ,e1)  
                 	(let* ([t (J e0 ctx)] [t2 (J e1 ctx)])

                 		(if (equal? t 'Bool)
                 			t2
                 			(error "condicion no bool"))) ]
                 [(primapp ,pr ,e* ...)
                  (let*
                      ([t (map (λ (x) (J x ctx)) e*)]
                       [b (map (λ (x) (equal? x 'Int)) t)])
                    (cond
                      [(and (arit? pr) (foldr (λ (x y) (and x y)) #t b))'Int]
                      [(equal? pr 'car) (caddr (car t))]
                      [(equal? pr 'cdr) (car t)]
                      [(equal? pr 'length) 'Int]
                      [(arit-bool? pr) 'Bool]))]
                 [(letrec ([,x ,t ,e]) ,body)
                  (let*
                      ([new-ctx (set-add  ctx (cons x t))]
                    [t0 (J e new-ctx)]
                    [s (J body new-ctx)])
                    (if (and (unify t t0) (not (equal? s 'Void)))
                        s
                        (error "El tipo no corresponde con el valor")))]
                 [(letfun ([,x ,t ,e]) ,body)
                  (let*
                      ([new-ctx (set-add ctx (cons x t))]
                    [t0 (J e ctx)]
                    [s (J body new-ctx)])
                    (if (and (unify t t0) (equal? (cadr t) '→))
                        s
                        (error "El tipo no corresponde con el valor")))]
                 [(,e0 ,e1) 
                  (let*
                    ([t0 (J e0 ctx)]
                     [t1 (J e1 ctx)])
                      (if (and (unify t0 `(,t1 → ,(caddr t0))) (funcion? t0))
                      (caddr t0)
                      (error "El tipo no corresponde con el valor")))]))

;;Este proceso  se encarga de quitar la anotación de tipo Lambda y sustituirlas por el tipo ’(T → T)
;; que corresponda a la definición de la función. Y sustituye las anotaciones de tipo List por el tipo (List of T)
(define-pass type-infer : L10(ir) -> L10()
  (definitions
    (define (re-type expr ctx)
      (nanopass-case (L10 Expr) expr
                     [,x x]
                     [(const ,t ,c) `(const ,t ,c)]
                     [(begin ,e* ... ,e)
                      (append '(begin) (map (lambda (ex) (re-type ex ctx)) e*) `(,(re-type e ctx)))]
                     [(primapp ,pr ,e* ...)
                      (append  `(primapp ,pr) (map (lambda (ex) (re-type ex ctx)) e*))]
                     [(if ,e0 ,e1 ,e2)
                      `(if ,(re-type e0 ctx) ,(re-type e1 ctx) ,(re-type e2 ctx))]
                     [(lambda ([,x ,t]) ,body)
                      `(lambda ([,x ,t]) ,(re-type body ctx))]
                     [(while [,e0] ,e1)
                      `(while [,(re-type e0 ctx)] ,(re-type e1 ctx))]
                     [(define ,x ,e) `(define ,(re-type x ctx) ,(re-type e ctx))]
                     [(let ([,x ,t ,e]) ,body)
                      (let ([tx (J e ctx)])
                        `(let ([,x ,tx ,(re-type e ctx)]) ,(re-type body (set-add ctx (cons x tx)))))]
                     [(letrec ([,x ,t, e]) ,body)
                      (let* ([tx (J e (set-add ctx (cons x t)))]
                               [nctx (set-add ctx (cons x tx))])
                        `(letrec ([,x ,tx ,(re-type e nctx)]),(re-type body nctx)))]
                     [(letfun ([,x ,t ,e]) ,body)
                      (let ([tx (J e ctx)])
                        `(letfun ([,x ,tx ,(re-type e ctx)]) ,(re-type body (set-add ctx (cons x tx)))))]
                     [(list ,e* ...)
                      (cons 'list (map (lambda (ex) (re-type ex ctx)) e*))]
                     [(,e0 ,e1)
                      `(,(re-type e0 ctx) ,(re-type e1 ctx))])))    
  (Expr : Expr(ir) -> Expr()
        [else (parser-L10 (re-type ir '()))]))


;Proceso uncurry encargado de descurrificar las expresiones lambda de nuestro lenguaje.
(define-pass uncurry : L10(ir) -> L11()
  (definitions
    (define (re-uncurry expr lst)
      (nanopass-case (L10 Expr) expr                    
                     [(lambda ([,x ,t]) ,body)
                        (let* ([a x] [b t] [mylist (cons (cons a (cons b '())) '())])
                          (re-uncurry body (append mylist lst)))]
                     [else `(lambda ,lst ,(unparse-L10 expr))])))    
  (Expr : Expr(ir) -> Expr()
        [else  (parser-L11 (re-uncurry ir '()))]))



;;Pruebas
;(assigment (parser-L11 '(letrec ([foo (Int → Int) (lambda ([ x Int ]) x) ])(foo (const Int 5)))))

;; Función que realiza el proceso de front-end del compilador
(define (front-end archivo texto)
  (let* ([exp ""])
    (if (= (length archivo) 1)
        (begin
          (set! exp (unparse-L8 (verify-arity
                  (un-anonymous
                   (identify-assigments
                    (curry-let
                     (direct-app
                      (purify-recursion
                       (quote-const
                        (eta-expand
                         (remove-logical-operators
                          (change-language
                           (remove-string
                            (remove-one-armed-if
                             (make-explicit(parser-LF (cadar archivo)))))))))))))))))
          
          (set! texto (string-append texto "'" (~a exp)))
          (escribe 1 texto))
        (begin
          (set! exp (unparse-L8(verify-arity
                 (un-anonymous
                  (identify-assigments
                   (curry-let
                    (direct-app
                     (purify-recursion
                      (quote-const
                       (eta-expand
                        (remove-logical-operators
                         (change-language
                          (remove-string
                           (remove-one-armed-if
                            (make-explicit (parser-LF (cadar archivo)))))))))))))))))
          
          (set! texto (string-append texto "'" (~a exp) "\n"))
          (front-end (cdr archivo) texto)))))


;; Proceso que se encarga de aplicar los procesos hasta el middl-end del compilador
(define (middle-end archivo texto)
  (let* ([exp ""])
    (if (= (length archivo) 1)
        (begin
          (set! exp (uncurry(type-infer(type-const(curry
                     (verify-arity
                      (un-anonymous
                       (identify-assigments
                        (curry-let
                         (direct-app
                          (purify-recursion
                           (quote-const
                            (eta-expand
                             (remove-logical-operators
                              (change-language
                               (remove-string
                                (remove-one-armed-if
                                 (make-explicit(parser-LF (cadar archivo))))))))))))))))))))
          
          (set! texto (string-append texto "'" (~a exp)))
          (escribe 2 texto))
        (begin
          (set! exp (uncurry(type-infer(type-const(curry(verify-arity
                 (un-anonymous
                  (identify-assigments
                   (curry-let
                    (direct-app
                     (purify-recursion
                      (quote-const
                       (eta-expand
                        (remove-logical-operators
                         (change-language
                          (remove-string
                           (remove-one-armed-if
                            (make-explicit (parser-LF (cadar archivo))))))))))))))))))))
          
          (set! texto (string-append texto "'" (~a exp) "\n"))
          (middle-end (cdr archivo) texto)))))



;; Función que escribe los archivos del .fe, .me y .c
(define (escribe num texto)
  (cond
    [(= 1 num) (write-file "archivo.fe" texto)]
    [(= 2 num) (write-file "archivo2.me" texto)]))



;; Función encargada de leer los archivos .mt que serán compilados
(define (ejecuta)
   (begin
      (display "Ingresa el nombre de tu archivo con extensión .mt o escribe exit para salir \n" )
      (define x (read-line (current-input-port) 'any))
      (if (equal? x "exit")
          (exit)
          (begin
            (front-end (file->list x) "")
            (middle-end (file->list x) "")
            (exit)))))

;; Llamada a la función que ejecuta el compilador
(ejecuta)
