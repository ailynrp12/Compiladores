#lang nanopass

(require nanopass/base)
(require racket/set)

;;PREDICADOS

(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x) (memq x '(+ - * / length car cdr and or not)))

(define (constant? x)
  (or (integer? x)
      (char? x)
      (boolean? x)))

(define (type? x) (memq x '(Bool Char Int List String Lambda)))

;; Predicado de primitiva
(define (primitiva? x) (memq x '(+ - * / length car cdr)))
;; Predicado de cuote
(define (cuote? x) (constant? x))
;; Contador global
(define count 0)
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
  (terminals
   (- (constant (c)))
   (+ (cuote (c))))
  (Expr (e body)
        (- c)
        (+ c)))

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


;; Práctica 4
;; Ejercicio 1
;; Proceso que currifica las expresiones let y letrec
(define-pass curry-let : L6 (ir) -> L7 ()
  (definitions
    (define  (curry vars tips exps body op)
      (cond
        [(empty vars) (unparse-L7 body)]
        [else `(,op ([,(car vars) ,(car tips) ,(car exps)])
                    ,(curry (cdr vars) (cdr tips) (cdr exps) body op))])))
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x* ,t* ,[e*]] ...) ,[body]) (parser-L7 (curry x* t* e* body 'let))]
        [(letrec ([,x* ,t* ,[e*]] ...) ,[body]) (parser-L7 (curry x* t* e* body 'letrec))]))

;; Ejercicio 2
;; Proceso que detecta los let que definen funciones y los reemplaza por un letrec
(define-pass identify-assigments : L7 (ir) -> L7 ()
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body]) (if (equal? t 'Lambda) `(letrec ([,x ,t ,e]) ,body)
                                     ir)]))

;; Ejercicio 3
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

;;Ejercicio 4
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
                 [(begin ,e* ... ,e) (set-union (FV e) (foldr set-union '() (map FV e*)))]
                 [(primapp ,pr ,e* ...) (foldr set-union '() (map FV e*))]
                 [(list ,e* ...)(foldr set-union '() (map FV e*))]
                 [(if ,e0 ,e1 ,e2) (set-union (FV e0) (FV e1) (FV e2))]
                 [(lambda ([,x* ,t*] ...) ,body) (set-remove (FV body) x*)]
                 [(let ([,x ,t ,e]) ,body) (set-union (set-remove (FV body) x) (FV e))]
                 [(letrec ([,x ,t ,e]) ,body) (set-union (set-remove (FV body) x) (FV e))]
                 [(letfun ([,x ,t ,e]) ,body) (set-union (set-remove (FV body) x) (FV e))]
                 [(,e0 ,e1 ...)(set-union (FV e0) (foldr set-union '() (map FV e1)))]))


;; Ejercicio 5
;; Proceso que se encarga de verificar que las expresiones no tengan variables libres
(define-pass verify-vars : L8 (ir) -> L8 ()
  (Expr : Expr (ir) -> Expr ()
        [else (let ([fv (FV ir)])
                (if (empty? fv) ir
                    (error (string-append "Free var " (symbol->string (car fv))))))]))
