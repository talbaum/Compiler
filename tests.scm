(define caar (lambda (pair) (car (car pair))))
(define cadr (lambda (pair) (car (cdr pair))))
(define cddr (lambda (pair) (cdr (cdr pair))))
(define cdar (lambda (pair) (cdr (car pair))))
(define caaar (lambda (pair) (car (caar pair))))
(define caadr (lambda (pair) (cdr (car pair))))
(define cdaar (lambda (pair) (cdr (caar pair))))
(define cdadr (lambda (pair) (cdr (cadr pair))))
(define cddar (lambda (pair) (cdr (cdar pair))))
(define cdddr (lambda (pair) (cdr (cddr pair))))
"================== Start: even and odd ==============="
(define even?
          (lambda (x)
            (or (= x 0)
                (odd? (- x 1)))))
(define odd?
 (lambda (x)
   (and (not (= x 0))
        (even? (- x 1)))))
(even? 5)
(even? 4)
(odd? 2)
(odd? 15)
"================== End: even and odd ==============="

"================== Start: list-ref ==============="

(define list-ref
    (lambda (ls n)
      (if (= n 0)
          (car ls)
          (list-ref (cdr ls) (- n 1))))) 

(list-ref '(a b c) 0)
(list-ref '(a b c) 1) 
(list-ref '(a b c) 2)

"================== End: list-ref ==============="

"================== Start: list-tail ==============="
(define list-tail
    (lambda (ls n)
      (if (= n 0)
          ls
          (list-tail (cdr ls) (- n 1))))) 




(list-tail '(a b c) 0)
(list-tail '(a b c) 2)
(list-tail '(a b c) 3) 
(list-tail '(a b c . d) 2)
(list-tail '(a b c . d) 3) 
(let ([x (list 1 2 3)])
  (eq? (list-tail x 2)
       (cddr x)))

"================== End: list-tail ==============="

"================== Start: list? ==============="
(define list?
(lambda (x)
  (letrec ([race
            (lambda (h t)
              (if (pair? h)
                  (let ([h (cdr h)])
                    (if (pair? h)
                        (and (not (eq? h t))
                             (race (cdr h) (cdr t)))
                        (null? h)))
                  (null? h)))])
    (race x x))))

(define make-cyclic-pair (lambda (first second) 
        (let ([lst (list first second '())])
         (set-cdr! (cdr lst) lst) lst)))

(define cyc-pair (make-cyclic-pair 'a 1))
(list? cyc-pair)
(list? '(1 2 3 4 6 6 8 #\a "ef"))

"================== End: list? ==============="

"================== Start: reverse ==============="

(define reverse
    (lambda (ls)
      (letrec ([rev (lambda (ls new)
        (if (null? ls)
            new
            (rev (cdr ls) (cons (car ls) new))))])
        (rev ls '()))))

(reverse '(1 2 3 4))
(reverse '(12 4 "sf" #t))

"================== End: reverse ==============="

"================== Start: memq ==============="
(define memq
    (lambda (x ls)
      (cond
        [(null? ls) #f]
        [(eq? (car ls) x) ls]
        [else (memq x (cdr ls))])))


(memq 'a '(b c a d e))
(memq 'a '(b c d e g)) 
    
(define count-occurrences
  (lambda (x ls)
    (cond
      [(memq x ls) =>
       (lambda (ls)
         (+ (count-occurrences x (cdr ls)) 1))]
      [else 0])))

(count-occurrences 'a '(a b c d a))
"================== End: memq ==============="


"================== Start: member ==============="

(define member
    (lambda (x ls)
      (cond
        [(null? ls) #f]
        [(equal? (car ls) x) ls]
        [else (member x (cdr ls))])))
(member '(b) '((a) (b) (c)))
(member '(d) '((a) (b) (c))) 
(member "b" '("a" "b" "c"))



(define member?
    (lambda (x ls)
      (and (member x ls) #t)))
  (member? '(b) '((a) (b) (c)))

"================== End: member ==============="


"================== Start: memp ==============="
(define memp (lambda (p lst)
        (if (null? lst)
            #f 
            (if (p (car lst))
                lst
                (memp p (cdr lst))))))

(memp odd? '(1 2 3 4))
(memp even? '(1 2 3 4))
(let ([ls (list 1 2 3 4)])
  (eq? (memp odd? ls) ls)) 
(let ([ls (list 1 2 3 4)])
  (eq? (memp even? ls) (cdr ls))) 
(memp odd? '(2 4 6 8))
"================== End: memp ==============="

"================== Start: remq ==============="
(define remq (lambda (obj lst)
        (if (null? lst)
        '()
        (let* ([hd (car lst)] [tl (cdr lst)] [rest (lambda () (remq obj tl))])
            (if (eq? obj hd)
                (rest)
                (cons hd (rest)))))))
(remq 'a '(a b a c a d))
(remq 'a '(b c d)) 
"================== End: remq ==============="


"================== Start: remove ==============="
(define remove (lambda (obj lst)
        (if (null? lst)
        '()
        (let* ([hd (car lst)] [tl (cdr lst)] [rest (lambda () (remove obj tl))])
            (if (equal? obj hd)
                (rest)
                (cons hd (rest)))))))


(remove '(b) '((a) (b) (c)))
"================== End: remove ==============="

"================== Start: filter ==============="
(define filter (lambda (p lst)
                (if (null? lst)
                '()
                (let* ([hd (car lst)] [tl (cdr lst)] [rest (lambda () (filter p tl))])
                    (if (p hd)
                        (cons hd (rest))
                        (rest))))))
(filter odd? '(1 2 3 4))
(filter
  (lambda (x) (and (> x 0) (< x 10)))
  '(-5 15 3 14 -20 6 0 -9))

"================== End: filter ==============="

"================== Start: remp ==============="

(define remp (lambda (p lst)
                (filter (lambda (x) (not (p x))) lst)))

(remp odd? '(1 2 3 4)) 
(remp
  (lambda (x) (and (> x 0) (< x 10)))
  '(-5 15 3 14 -20 6 0 -9)) 

"================== End: remp ==============="

"================== Start: find ==============="
(define find (lambda (p lst)
                (if (null? lst)
                #f
                (let* ([hd (car lst)] [tl (cdr lst)] [rest (lambda () (find p tl))])
                    (if (p hd)
                        hd
                        (rest))))))
        

(find odd? '(1 2 3 4)) 
(find even? '(1 2 3 4))
(find odd? '(2 4 6 8)) 
"================== End: find ==============="


"================== Start: assq ==============="
(define assq
    (lambda (x ls)
      (cond
        [(null? ls) #f]
        [(eq? (caar ls) x) (car ls)]
        [else (assq x (cdr ls))])))

(assq 'b '((a . 1) (b . 2)))
(cdr (assq 'b '((a . 1) (b . 2))))
(assq 'c '((a . 1) (b . 2)))
"================== End: assq ==============="

"================== Start: assoc ==============="

(define assoc
    (lambda (x ls)
      (cond
        [(null? ls) #f]
        [(equal? (caar ls) x) (car ls)]
        [else (assq x (cdr ls))])))

        


(assoc '(a) '(((a) . a) (-1 . b)))
(assoc '(a) '(((b) . b) (a . c)))

"================== End: assoc ==============="


"================== Start: assp ==============="

(define assp (lambda (p lst)
                (cond 
                    [(null? lst) #f]
                    [(p (caar lst)) (car lst)]
                    [else (assp p (cdr lst))])))

(assp odd? '((1 . a) (2 . b)))  
(assp even? '((1 . a) (2 . b)))  
(let ([ls (list (cons 1 'a) (cons 2 'b))])
  (eq? (assp odd? ls) (car ls))) 
(let ([ls (list (cons 1 'a) (cons 2 'b))])
  (eq? (assp even? ls) (cadr ls)))
(assp odd? '((2 . b))) 

"================== End: assp ==============="



"================== Start: char upcase and downcase ==============="
(define char-upcase (lambda (c) (integer->char (- (char->integer c) 32))))
(define char-downcase (lambda (c) (integer->char (+ (char->integer c) 32))))
(char-upcase #\a)
(char-upcase #\r)
(char-downcase #\A)

"================== End: char upcase and downcase ==============="

"================== Start: list->string ==============="
(define list->string
    (lambda (ls)
      (let* ( [i 0] [s (make-string (length ls))] )
            (letrec ([loop (lambda (ls i)
                (if  (null? ls)
                    s
                    (begin 
                        (string-set! s i (car ls)) 
                        (loop (cdr ls) (+ i 1)))))])
                    (loop ls i)))))
  (list->string '())
  (list->string '(#\a #\b #\c))
  (list->string '(#\s #\f #\s #\g #\g #\r #\e #\r))

  "================== End: list->string ==============="

  "================== Start: string->list ==============="
  (define string->list 
    (lambda (s)
    (let* ( [i 0] )
          (letrec ([loop (lambda (s i)
              (if  (= i (string-length s))
                  '()
                      (cons (string-ref s i) (loop s (+ i 1)))))])
                  (loop s i)))))
  
(string->list "")
(string->list "abc")
(map char-upcase (string->list "abc"))
(list->string (map char-downcase (string->list "SFSGGRER")))
"================== End: string->list ==============="

"================== Start: factorial ==============="
(define factorial
    (lambda (n)
    (letrec ([fact (lambda (i)
        (if (= i 0)
            1
            (* i (fact (- i 1)))))])
            (fact n))))
  
  (factorial 0)  
  (factorial 1) 
  (factorial 2)  
  (factorial 3) 
  (factorial 10)
  "================== End: factorial ==============="


  "================== Start: factorial-iter ==============="
  (define factorial-iter
    (lambda (n)
      (letrec ([fact (lambda (i a)
        (if (= i 0)
            a
            (fact (- i 1) (* a i))))])
            (fact n 1))))

  (factorial-iter 0)  
  (factorial-iter 1) 
  (factorial-iter 2)  
  (factorial-iter 3) 
  (factorial-iter 10)
"================== End: factorial-iter ==============="

"================== Start: product$ ==============="
(define product$
  (lambda (ls k)
    (let ([break k])
      (letrec ([f (lambda (ls k) 
        (cond
          [(null? ls) (k 1)]
          [(= (car ls) 0) (break 0)]
          [else (f (cdr ls)
                   (lambda (x)
                     (k (* (car ls) x))))]))])
        (f ls k)))))

(product$ '(1 2 3 4 5) (lambda (x) x))
(product$ '(7 3 8 0 1 9 5) (lambda (x) x))
(product$ '(7 3 8 1 1 912 5) (lambda (x) x))
"================== End: product$ ==============="

(define andmap (lambda (p lst)
        (or (null? lst)
            (and (p (car lst)) (andmap p (cdr lst)))) ))
; make-matrix creates a matrix (a vector of vectors).
 ; make-matrix creates a matrix (a vector of vectors).
 (define make-matrix
  (lambda (rows columns)
  (letrec ([loop (lambda (m i)
  (if (= i rows)
      (begin m)
      (begin
        (vector-set! m i (make-vector columns))
        (loop m (+ i 1)))))])
(loop (make-vector rows) 0)))) 

; matrix? checks to see if its argument is a matrix.
; It isn't foolproof, but it's generally good enough.
(define matrix?
  (lambda (x)
    (and (vector? x)
         (> (vector-length x) 0)
         (vector? (vector-ref x 0)))))

; matrix-rows returns the number of rows in a matrix.
(define matrix-rows
  (lambda (x)
    (vector-length x)))

; matrix-columns returns the number of columns in a matrix.
(define matrix-columns
  (lambda (x)
    (vector-length (vector-ref x 0))))

; matrix-ref returns the jth element of the ith row.
(define matrix-ref
  (lambda (m i j)
    (vector-ref (vector-ref m i) j)))

; matrix-set! changes the jth element of the ith row.
(define matrix-set!
  (lambda (m i j x)
    (vector-set! (vector-ref m i) j x)))

; mat-sca-mul multiplies a matrix by a scalar.
(define mat-sca-mul
  (lambda (x m)
    (let* ([nr (matrix-rows m)]
           [nc (matrix-columns m)]
           [r (make-matrix nr nc)])
           (letrec ([loop (lambda (i)
           (if (= i nr)
               (begin r)
               (begin
                  (letrec ([loop2 (lambda (j)
                  (if (= j nc)
                      #t
                      (begin
                        (matrix-set! r i j (* x (matrix-ref m i j)))
                        (loop2 (+ j 1)))))])
   (loop2 0))
                 (loop (+ i 1)))))])
(loop 0)))))

; mat-mat-mul multiplies one matrix by another, after verifying
; that the first matrix has as many columns as the second
; matrix has rows.
(define mat-mat-mul
  (lambda (m1 m2)
    (let* ([nr1 (matrix-rows m1)]
           [nr2 (matrix-rows m2)]
           [nc2 (matrix-columns m2)]
           [r (make-matrix nr1 nc2)])
           (letrec ([loop (lambda (i)
           (if (= i nr1)
               (begin r)
               (begin
                  (letrec ([loop (lambda (j)
                  (if (= j nc2)
                      #t
                      (begin
                          (letrec ([loop (lambda (k a)
                          (if (= k nr2)
                              (begin (matrix-set! r i j a))
                              (begin
                                (loop
                                  (+ k 1)
                                  (+ a
                                     (* (matrix-ref m1 i k)
                                        (matrix-ref m2 k j)))))))])
                              (loop 0 0))
                        (loop (+ j 1)))))])
                  (loop 0))
          (loop (+ i 1)))))])
(loop 0))))) 


   ; mul is the generic matrix/scalar multiplication procedure
   (define mul
    (lambda (x y)
      (cond
        [(number? x)
         (cond
           [(number? y) (* x y)]
           [(matrix? y) (mat-sca-mul x y)]
           [else "this should be an error, but you don't support exceptions"])]
        [(matrix? x)
         (cond
           [(number? y) (mat-sca-mul y x)]
           [(matrix? y) (mat-mat-mul x y)]
           [else "this should be an error, but you don't support exceptions"])]
        [else "this should be an error, but you don't support exceptions"])))


  (mul '#(#(2 3 4)
  #(3 4 5))
'#(#(1) #(2) #(3)))

(mul '#(#(1 2 3))
     '#(#(2 3)
        #(3 4)
        #(4 5)))

(mul '#(#(1 2 3)
        #(4 5 6))
     '#(#(1 2 3 4)
        #(2 3 4 5)
        #(3 4 5 6)))


(mul -2
  '#(#(3 -2 -1)
     #(-3 0 -5)
     #(7 -1 -1))
     )


     (mul 0.5 '#(#(1 2 3)) )
     (mul 1 0.5)
