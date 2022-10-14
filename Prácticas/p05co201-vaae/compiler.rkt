#lang nanopass

(define count 0)

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr)))

;; Predicado de primitiva
(define (primitiva? x) (memq x '(+ - * / length car cdr)))
;; Predicado de cuote
(define (cuote? x) (constant? x))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

;; SISTEMA DE TIPOS
;; Int | Char | Bool | Lambda | List | (List of T) | (T → T)
(define (type? x) (or (b-type? x) (c-type? x)))
;;Verifica si es un tipo basico
(define (b-type? x) (memq x '(Bool Char Int List String Lambda)))
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

;; PROCESOS

;Proceso que cambia el cuerpo de lambda, let y letrec por un begin.
(define-pass make-explicit : LF (ir) -> L0 ()
  (Expr : Expr (ir) -> Expr ()
    [,c `',c]
    [(lambda ([,x* ,t*] ...) ,[body*] ... ,[body])
     `(lambda ([,x* ,t*] ...) (begin ,body* ... ,body))]
    [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(let ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]
    [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body])
     `(letrec ([,x* ,t* ,e*] ...) (begin ,body* ... ,body))]))

;;Preproceso del compilador que transforma un if sin else a uno con else
;;Para esto se creó un nuevo lenguaje llamado LFV
(define-pass remove-one-armed-if : LF (ir) -> LFV ()
  (Expr : Expr (ir) -> Expr()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))

;;Preproceso del compilador que elimina las cadenas como elementos terminales
;;Para esto se creó un nuevo lenguaje llamado LFVS
(define-pass remove-string : LF (ir) -> L3 ()
  (Expr : Expr (ir) -> Expr()
        [,s (string->list s)]))

;; Proceso que elimina las primitivas and, or y not
(define-pass remove-logical-operators : LIF (ir) -> L4 ()
  (Expr : Expr (ir) -> Expr()
        [(not ,[e]) `(if ,e #f #t)]
        [(or ,[e0] ,[e1]) `(if ,e0 #t ,e1)]
        [(and ,[e0] ,[e1]) `(if ,e0 ,e1 #f)]))

;; Proceso que sustituye las primitivas por lambdas
(define-pass eta-expand : L4 (ir) -> L5 ()
  (Expr : Expr (ir) -> Expr ()
        [,c `,c]
        [,pr (if (or (equal? pr '+)
                     (equal? pr '-)
                     (equal? pr '*)
                     (equal? pr '/))`(lambda ([x Int] [y Int]) (primapp ,pr x y))
                 `(lambda ([x List]) (primapp ,pr x)))]
        [(list ,e* ,e) `(list ,e* ,e)]
        [(,[e0] ,[e1] ...) `(,e0 ,e1 ...)]))

;;Proceso que quotea las constante()s
(define-pass quote-const : L5 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr()
        [,c `(cuote ,c)]))

;; Procesos que purifica letrec
(define-pass purify-recursion : L6 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(letrec ([,x* ,t* ,[e*]] ...) ,body) (let currificacion ([variables x*] [tipos t*] [valores e*])
                                                (cond
                                                  [(and (= (length variables) 1) (equal? (car tipos) 'Lambda))
                                                   `(letrec ([,(car variables) ,(car tipos) ,(car valores)]) ,body)]
                                                  [(and (= (length variables) 1) (not (equal? (car tipos) 'Lambda)))
                                                   `(let ([,(car variables) ,(car tipos) ,(car valores)]) ,body)]
                                                  [(equal? (car tipos) 'Lambda)
                                                   `(letrec ([,(car variables) ,(car tipos) ,(car valores)])
                                                      ,(currificacion (cdr variables) (cdr tipos) (cdr valores)))]
                                                  [else `(let ([,(car variables) ,(car tipos) ,(car valores)])
                                                      ,(currificacion (cdr variables) (cdr tipos) (cdr valores)))]))]))

;;Proceso que convierte una lambda a un let
(define-pass direct-app : L6 (ir) -> L6 ()
  (Expr : Expr (ir) -> Expr ()
        [((lambda ([,x* ,t*] ...) ,[body]) ,[e0] ...) `((let [,x* ,t* ,e0] ...) ,body)]))

;; Proceso que currifica las expresiones let y letrec
(define-pass curry-let : L6 (ir) -> L7 ()
  (definitions
    (define  (curry vars tips exps body op)
      (cond
        [(empty? vars) (unparse-L7 body)]
        [else `(,op ([,(car vars) ,(car tips) ,(car exps)])
                    ,(curry (cdr vars) (cdr tips) (cdr exps) body op))])))
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x* ,t* ,[e*]] ...) ,[body]) (parser-L7 (curry x* t* e* body 'let))]
        [(letrec ([,x* ,t* ,[e*]] ...) ,[body]) (parser-L7 (curry x* t* e* body 'letrec))]))

;; Proceso que detecta los let que definen funciones y los reemplaza por un letrec
(define-pass identify-assigments : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body]) (if (equal? t 'Lambda) `(letrec ([,x ,t ,e]) ,body)
                                     ir)]))

;; Proceso que se encarga de asignar identificadores a las expresiones lambda
(define-pass un-anonymous : L7 (ir) -> L8 ()
  (definitions
    (define (new-name)
      (begin
        (define str (string-append "foo" (number->string count)))
        (set! count (+ 1 count))
        (string->symbol str))))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x* ,t*] ...) ,[body]) (let ([lam (new-name)])
                                            `(letfun ([,lam Lambda ,ir]) ,lam))]))

;; Proceso que se encarga de verificar la aridad de los operadores
(define-pass verify-arity : L8 (ir) -> L8 ()
  (definitions
    (define (arit? e) (memq e '(+ - * /)))
    (define (list? e) (memq e '(car cdr length))))
  (Expr : Expr(ir) -> Expr()
    [(primapp ,pr ,[e*] ...)
      (cond
        [ (and (arit? pr) (equal? (length e*) 2)) ir]
        [ (and (list? pr) (equal? (length e*) 1)) ir]
        [ else (error "Arity mismatch")])]))

;; Función auxiliar que nos ayuda a identificar las variables libres en las expresiones
(define (FV exp)
  (nanopass-case (L8 Expr) exp
                 [,x `(,x)]
                 [,c `()]
                 [,pr `()]
                 [(cuote ,c) `()]
                 [(begin ,e* ... ,e) (set-union (FV e) (foldr set-union '() (map FV e*)))]
                 [(primapp ,pr ,e* ...) (foldr set-union '() (map FV e*))]
                 [(list ,e* ...)(foldr set-union '() (map FV e*))]
                 [(if ,e0 ,e1 ,e2) (set-union (FV e0) (FV e1) (FV e2))]
                 [(lambda ([,x* ,t*] ...) ,body) (set-remove (FV body) x*)]
                 [(let ([,x ,t ,e]) ,body) (set-union (set-remove (FV body) x) (FV e))]
                 [(letrec ([,x ,t ,e]) ,body) (set-union (set-remove (FV body) x) (FV e))]
                 [(letfun ([,x ,t ,e]) ,body) (set-union (set-remove (FV body) x) (FV e))]
                 [(,e0 ,e1 ...)(set-union (FV e0) (foldr set-union '() (map FV e1)))]))


;; Proceso que se encarga de verificar que las expresiones no tengan variables libres
(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [else (let ([fv (FV ir)])
                (if (empty? fv) ir
                    (error (string-append "Free var " (symbol->string (car fv))))))]))

;; Práctica 5
;; Sección 1
;; Ejercicio 1
;; Proceso que se encarga de currificar las expresiones lambda así como las aplicaciones de función.
(define-pass curry : L8 (ir) -> L9 ()
  (definitions
    (define  (currifica vars tips body op)
      (cond
        [(empty? vars) (unparse-L9 body)]
        [else `(,op ([,(car vars) ,(car tips)])
                    ,(currifica (cdr vars) (cdr tips) body op))])))
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x* ,t*] ...) ,[body]) (parser-L9(currifica x* t* body 'lambda))]
        [(,e0 ,e1 ...) (let ([param (car(reverse e1))]
                             [fun (append (cdr(reverse e1)) (cons e0 '()))])
                         (let curry-app ([a  param][b fun])
                           (if (null? b) a
                               `(,(curry-app (car b) (cdr b)) ,a ))))]))
        

;; Ejercicio 2
;; Proceso que se encarga de colocar las anotaciones de tipos correspondientes a las constantes
(define-pass type-const : L9 (ir) -> L10 ()
  (Expr : Expr (ir) -> Expr ()
        [(cuote ,c) (cond
                      [(boolean? c) `(const Bool ,c)]
                      [(integer? c) `(const Int ,c)]
                      [else `(const Char ,c)])]))

;; Sección 2 Inferencia de tipos
;; Ejercicio 1
;; Implementación del algoritmo J que devuelve un tipo o un error
(define (J expr ctx)
  (nanopass-case (L10 Expr) expr
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
                 [(lambda ([,x ,t]) ,body)
                 	(let*
                            ([new-ctx (set-add  ctx (cons x t))]
                             [s (J body new-ctx)])
                          `(,t → ,s))]
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


;; Ejercicio 2
;; Proceso que se encarga de quitar la anotación de tipo Lambda y las anotaciones del tipo List
(define-pass type-infer : L10 (ir) -> L10 ()
  (Expr : Expr (ir) -> Expr ()
        [(lambda ([,x ,t]) ,[body]) `(lambda ([,x ,t]) ,body)]
        [(let ([,x ,t ,[e]]) ,[body]) `(let ([,x ,(J e '()) ,e]) ,body)]
        [(letrec ([,x ,t ,[e]]) ,[body]) (cond
                                       [(or (equal? t 'Lambda) (equal? t 'List))
                                        `(letrec ([ ,x ,(J e '()) ,e ]) ,body)]
                                       [else ir])]
        [(letfun ([,x ,t ,[e]]) ,[body]) `(letfun ([,x ,(J e '()) ,e]) ,body)]))


;; Función auxiliar que busca un par de variable y tipo en el contexto
;; Si no está regresa un error
(define (look-up var ctx)
 	(cond 
 		[(null? ctx) (error "Sin tipo")]
 		[(equal? var (caar ctx))(cdar ctx)]
 		[else (look-up var (cdr ctx))]))

;; Función auxiliar que verifica si un tipo corresponde a una función
;; Regresa true si es así y en otro caso false
(define (esFuncion? x)
  (if (list? x)
      (let* ([f (car x)]
             [s (cadr x)]
             [t (caddr x)])
        (and (type? f) (equal? s '→) (type? t)))
	#f))

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

;; PRUEBAS PARA LA FUNCIÓN J				
(J (parser-L10 'x) `( ,(cons 'x 'Int)))
;; Salida : 'Int
(J (parser-L10 '(const Int 5)) '())
;; Salida : 'Int
(J (parser-L10 '(begin x x x (const Int 5) x x x x (const Bool #t))) `( ,(cons 'x 'Int)))
;; Salida : 'Bool
(J (parser-L10 '(primapp + (const Int 6) (const Int 5))) '())
;; Salida : 'Int
(J (parser-L10 '(primapp cdr (list (const Int 6) (const Int 5)))) '())
;; Salida : '(List of Int)
(J (parser-L10 '(primapp car (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
(J (parser-L10 '(primapp length (list (const Int 6) (const Int 5)))) '())
;; Salida : 'Int
(J (parser-L10 '(if (const Bool #t) x (const Int 5))) `( ,(cons 'x 'Int)))
;; Salida : 'Int
(J (parser-L10 '(lambda ([x Int]) x)) '())
;; Salida : '(Int → Int)
(J (parser-L10 '(let ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
(J (parser-L10 '(letrec ([x Int (const Int 5)]) x)) '())
;; Salida : 'Int
(J (parser-L10 '(list)) '())
;; Salida : 'List
(J (parser-L10 '(list (const Bool #t) (const Bool #f))) '())
;; Salida : '(List of Bool)
(J (parser-L10 '(list (list) (list (const Bool #f) (const Bool #t)))) '())
;; Salida : '(List of (List of Bool))
;; CASOS DE ERROR
;(J (parser-L10 '(list (const Int 5) (const Bool #f))) '())
;; Salida : error : Listas homogeneas
;(J (parser-L10 '(list (list) (list (list (const Bool #t) (const Bool #f))) (list (list (const Int 5) (const Int 6))))) '())
;; Salida : error : Listas homogeneas
;(parser-L10 '(t (List of Int)))
