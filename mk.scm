(define c->S (lambda (c) (car c)))

(define c->D (lambda (c) (cadr c)))

(define c->A (lambda (c) (caddr c)))

(define c->T (lambda (c) (cadddr c)))

(define empty-c '(() () () ()))

(define-syntax lambdag@
  (syntax-rules (:)
    ((_ (c) e) (lambda (c) e))
    ((_ (c : S D A T) e)
     (lambda (c)
       (let ((S (c->S c))
             (D (c->D c))
             (A (c->A c))
             (T (c->T c)))
         e)))))

(define mzero (lambda () #f))

(define unit (lambdag@ (c) c))

(define choice (lambda (c f) (cons c f)))

(define-syntax lambdaf@ 
  (syntax-rules () ((_ () e) (lambda () e))))

(define-syntax inc 
  (syntax-rules () ((_ e) (lambdaf@ () e))))

(define empty-f (lambdaf@ () (mzero)))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((c-inf e))
       (cond
         ((not c-inf) e0)
         ((procedure? c-inf)  (let ((f^ c-inf)) e1))
         ((not (and (pair? c-inf)
                 (procedure? (cdr c-inf))))
          (let ((c^ c-inf)) e2))
         (else (let ((c (car c-inf)) (f (cdr c-inf))) 
                 e3)))))))

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
       (lambdaf@ ()
         ((fresh (x) g0 g ...
            (lambdag@ (final-c)
              (let ((z ((reify x) final-c)))
                (choice z empty-f))))
          empty-c))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f) 
         (() '())
         ((f) (take n f))
         ((c) (cons c '()))
         ((c f) (cons c (take (and n (- n 1)) f))))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (c)
       (inc (let ((x (var 'x)) ...)
              (bind* (g0 c) g ...)))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (lambdaf@ () (bind (f) g)))))))

(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (lambdaf@ () (mplus (f) f^)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c) (inc (mplus* (bind* (g0 c) g ...)
                                (bind* (g1 c) g^ ...) ...))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0 (lambdaf@ () (mplus* e ...))))))

(define-syntax case-value
  (syntax-rules ()
    ((_ u ((t1) e0) ((at dt) e1) ((t2) e2))
     (let ((t u))
       (cond
	 ((var? t) (let ((t1 t)) e0))
	 ((pair? t) (let ((at (car t)) (dt (cdr t))) e1))
	 (else (let ((t2 t)) e2)))))))

(define make-tag-A
  (lambda (tag pred)
    (lambda (u)
      (lambdag@ (c : S D A T)
        (case-value (walk u S)
          ((x) (cond
                 ((make-tag-A+ x tag pred c S D A T) =>
                  unit)
                 (else (mzero))))
          ((au du) (mzero))
          ((u) (cond
                 ((pred u) (unit c))
                 (else (mzero)))))))))

(define make-tag-A+
  (lambda (u tag pred c S D A T)
    (cond
      ((ext-A (walk u S) tag pred S A) => 
       (lambda (A+)  
         (cond
           ((null? A+) c)
           (else (let ((D (subsume A+ D))
                       (A (append A+ A)))
                   (subsume-A S D A T))))))
      (else #f))))

(define subsume-A
  (lambda (S D A T)
    (let ((x* (rem-dups (map lhs A))))
      (subsume-A+ x* S D A T))))

(define subsume-A+
  (lambda (x* S D A T)
    (cond
      ((null? x*) `(,S ,D ,A ,T))
      (else (let ((x (car x*)))
              (let ((D/T (update-D/T x S D A T)))
                (let ((D (car D/T)) (T (cdr D/T)))
                  `(,S ,D ,A ,T))))))))

(define ext-A 
  (lambda (x tag pred S A)
    (cond
      ((null? A) `((,x . (,tag . ,pred))))
      (else
       (let ((a (car A)) (A (cdr A)))
         (let ((a-tag (pr->tag a)))
           (cond
             ((eq? (walk (lhs a) S) x)
              (cond
                ((tag=? a-tag tag) '())
                (else #f)))
             (else (ext-A x tag pred S A)))))))))

(define symbolo (make-tag-A 'sym symbol?))

(define numbero (make-tag-A 'num number?))

(define booleano
  (lambda (x)
    (conde
      ((== #f x))
      ((== #t x)))))

(define pr->tag (lambda (pr) (car (rhs pr))))

(define pr->pred (lambda (pr) (cdr (rhs pr))))

(define =/= 
  (lambda (u v)
    (lambdag@ (c : S D A T)
      (cond
        ((unify u v S) => (post-unify-=/= S D A T))
        (else (unit c))))))

(define post-unify-=/=
  (lambda (S D A T)
    (lambda (S+)
      (cond
        ((eq? S+ S) (mzero))
        (else (let ((D+ (list (prefix-S S+ S))))
                (let ((D+ (subsume A D+)))
                  (let ((D+ (subsume T D+)))
                    (let ((D (append D+ D)))
                      (unit `(,S ,D ,A ,T)))))))))))

(define prefix-S
  (lambda (S+ S)
    (cond
      ((eq? S+ S) '())
      (else (cons (car S+) (prefix-S (cdr S+) S))))))

(define subsume
  (lambda (A/T D)
    (remp (lambda (d) (exists (subsumed-pr? A/T) d))
      D)))

(define subsumed-pr?
  (lambda (A/T)
    (lambda (pr-d)
      (let ((u (rhs pr-d)))
        (cond
          ((var? u) #f)
          (else
           (let ((pr (assq (lhs pr-d) A/T)))
             (and pr
               (let ((tag (pr->tag pr)))
                 (cond
                   ((and (tag? tag)
                         (tag? u)
                         (tag=? u tag)))
                   (((pr->pred pr) u) #f)
                   (else #t)))))))))))

(define == 
  (lambda (u v)
    (lambdag@ (c : S D A T)
      (cond
        ((unify u v S) =>
         (post-unify-== c S D A T))
        (else (mzero))))))

(define post-unify-==
  (lambda (c S D A T)
    (lambda (S+)
      (cond
        ((eq? S+ S) (unit c))
        ((verify-D D S+) =>
         (lambda (D)
           (cond
             ((post-verify-D S+ D A T) => unit)
             (else (mzero)))))
        (else (mzero))))))

(define verify-D
  (lambda (D S)
    (cond
      ((null? D) '())
      ((verify-D (cdr D) S) =>
       (lambda (D+)
         (verify-D+ (car D) D+ S)))
      (else #f))))

(define verify-D+ 
  (lambda (d D S)
    (cond
      ((unify* d S) =>
       (lambda (S+)
         (cond
           ((eq? S+ S) #f)
           (else (cons (prefix-S S+ S) D)))))
      (else D))))

(define post-verify-D
  (lambda (S D A T)
    (cond
      ((verify-A A S) =>
       (post-verify-A S D T))
      (else #f))))

(define verify-A
  (lambda (A S)
    (cond
      ((null? A) '())
      ((verify-A (cdr A) S) =>
       (lambda (A0)
         (let ((u (walk (lhs (car A)) S))
               (tag (pr->tag (car A)))
               (pred (pr->pred (car A))))
           (cond
             ((var? u)
              (cond
                ((ext-A u tag pred S A0) =>
                 (lambda (A+)
                   (append A+ A0)))
                (else #f)))
             (else (and (pred u) A0))))))
      (else #f))))

(define post-verify-A
  (lambda (S D T)
    (lambda (A)
      (let ((D (subsume A D)))
        (cond
          ((verify-T T S) => (post-verify-T S D A))
          (else #f))))))

(define verify-T 
  (lambda (T S)
    (cond
      ((null? T) '())
      ((verify-T (cdr T) S) => (verify-T+ (lhs (car T)) T S))
      (else #f))))

(define verify-T+
  (lambda (x T S)
    (lambda (T0)
      (let ((tag (pr->tag (car T)))
            (pred (pr->pred (car T))))
	(case-value (walk x S)
	  ((x) (cond
                 ((ext-T+ x tag pred S T0) =>
                  (lambda (T+) (append T+ T0)))
                 (else #f)))
          ((au du) (cond
                     (((verify-T+ au T S) T0) =>
                      (verify-T+ du T S))
                     (else #f)))
          ((u) (and (pred u) T0)))))))

(define post-verify-T
  (lambda (S D A)
    (lambda (T)
      (subsume-T T S (subsume T D) A '()))))

(define subsume-T  
  (lambda (T+ S D A T)
    (let ((x* (rem-dups (map lhs A))))
      (subsume-T+ x* T+ S D A T))))

(define subsume-T+ 
  (lambda (x* T+ S D A T)
    (cond
      ((null? x*)
       (let ((T (append T+ T)))
         `(,S ,D ,A ,T)))
      (else
       (let ((x (car x*)) (x* (cdr x*)))
         (let ((D/T (update-D/T x S D A T+)))
           (let ((D (car D/T)) (T+ (cdr D/T)))
             (subsume-T+ x* T+ S D A T))))))))

(define update-D/T
  (lambda (x S D A T)
    (cond
      ((null? A)
       (let ((T (remp (lambda (t)
                        (eq? (lhs t) x))
                  T)))
         `(,D . ,T)))
      (else
       (let ((a (car A)))
         (cond
           ((and (eq? (lhs a) x)
              (or (tag=? (pr->tag a) 'sym)   
                  (tag=? (pr->tag a) 'num)))
            (update-D/T+ x '() S D T))
           (else
	    (update-D/T x S D (cdr A) T))))))))

(define update-D/T+
  (lambda (x T+ S D T)
    (cond
      ((null? T)
       `(,D . ,T+))
      (else
       (let ((t (car T))
             (T (cdr T)))
         (cond
           ((eq? (lhs t) x)
            (let ((D (ext-D x (pr->tag t) D S)))
              (update-D/T+ x T+ S D T)))
           (else
            (let ((T+ (cons t T+)))
              (update-D/T+ x T+ S D T)))))))))

(define ext-D
  (lambda (x tag D S)
    (cond
      ((exists 
         (lambda (d)
           (and (null? (cdr d))
             (let ((y (lhs (car d)))
                   (u (rhs (car d))))
               (and
                 (eq? (walk y S) x)
                 (tag? u)
                 (tag=? u tag))))) 
         D)
       D)
      (else (cons `((,x . ,tag)) D)))))

(define absento 
  (lambda (tag u)
    (cond
      ((not (tag? tag)) fail)
      (else
       (lambdag@ (c : S D A T)
         (cond
           ((absento+ u tag c S D A T) => unit)
           (else (mzero))))))))

(define absento+  
  (lambda (u tag c S D A T)
    (case-value (walk u S)
      ((x)
       (let ((T+ (ext-T x tag S T)))
         (cond
           ((null? T+) c)
           (else
            (let ((D (subsume T+ D)))
              (subsume-T T+ S D A T))))))
      ((au du)
       (let ((c (absento+ au tag c S D A T)))
         (and c
           (let ((S (c->S c))
                 (D (c->D c))
                 (A (c->A c))
                 (T (c->T c)))
             (absento+ du tag c S D A T)))))
      ((u)
       (cond
         ((and (tag? u) (tag=? u tag)) #f)
         (else c))))))

(define ext-T 
  (lambda (x tag S T)
    (cond
      ((null? T)
       (let ((pred (make-pred-T tag)))
         `((,x . (,tag . ,pred)))))
      (else
       (let ((t (car T)) (T (cdr T)))
         (let ((t-tag (pr->tag t)))
           (cond
             ((eq? (walk (lhs t) S) x)
              (cond
                ((tag=? t-tag tag) '())
                (else (ext-T x tag S T))))
             ((tag=? t-tag tag)
              (let ((t-pred (pr->pred t)))
                (ext-T+ x tag t-pred S T)))
             (else (ext-T x tag S T)))))))))

(define ext-T+ 
  (lambda (x tag pred S T)
    (cond
      ((null? T) `((,x . (,tag . ,pred))))
      (else
       (let ((t (car T)))
         (let ((t-tag (pr->tag t)))
           (cond
             ((eq? (walk (lhs t) S) x)
              (cond
                ((tag=? t-tag tag) '())
                (else
                 (ext-T+ x tag pred S
                   (cdr T)))))
             (else
              (ext-T+ x tag pred S
                (cdr T))))))))))

(define make-pred-T
  (lambda (tag)
    (lambda (x)
      (not (and (tag? x) (tag=? x tag))))))

(define tag?
  (lambda (tag)
    (symbol? tag)))

(define tag=?
  (lambda (tag1 tag2)
    (eq? tag1 tag2)))

(define var (lambda (dummy) (vector dummy)))

(define var? (lambda (x) (vector? x)))

(define rem-dups
  (lambda (x*)
    (cond
      ((null? x*) '())
      ((memq (car x*) (cdr x*))
       (rem-dups (cdr x*)))
      (else (cons (car x*)
              (rem-dups (cdr x*)))))))

(define lhs (lambda (pr) (car pr)))

(define rhs (lambda (pr) (cdr pr)))

(define succeed (== #f #f))

(define fail (== #f #t))

(define walk
  (lambda (u S)
    (cond
      ((and (var? u) (assq u S)) =>
       (lambda (pr) (walk (rhs pr) S)))
      (else u))))

(define unify
  (lambda (u v S)
    (let ((u (walk u S)) (v (walk v S)))
      (cond
        ((and (pair? u) (pair? v))
         (let ((S (unify (car u) (car v) S)))
           (and S (unify (cdr u) (cdr v) S))))
        (else (unify-nonpair u v S))))))

(define unify-nonpair
  (lambda (u v S)
    (cond
      ((eq? u v) S)
      ((var? u) (ext-S u v S))
      ((var? v) (ext-S v u S))
      ((equal? u v) S)
      (else #f))))

(define ext-S
  (lambda (x v S)
    (case-value v
      ((y) (cons `(,x . ,y) S))
      ((au du) (cond
                 ((occurs-check x v S) #f)
                 (else (cons `(,x . ,v) S))))
      ((v) (cons `(,x . ,v) S)))))

(define occurs-check
  (lambda (x v S)
    (case-value (walk v S)
      ((y) (eq? y x))
      ((av dv) (or (occurs-check x av S)
                   (occurs-check x dv S)))
      ((v) #f))))

(define walk*
  (lambda (v S)
    (case-value (walk v S)
      ((x) x)
      ((av dv)
       (cons (walk* av S) (walk* dv S)))
      ((v) v))))

(define reify-S
  (lambda (v S)
    (case-value (walk v S)
      ((x) (let ((n (length S)))
             (let ((name (reify-name n)))
               (cons `(,x . ,name) S))))
      ((av dv) (let ((S (reify-S av S)))
                 (reify-S dv S)))
      ((v) S))))

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define reify
  (lambda (x)
    (lambda (c)
      (let ((S (c->S c)) (D (c->D c))
            (A (c->A c)) (T (c->T c)))
        (let ((v (walk* x S)))
          (let ((S (reify-S v '())))
            (reify+ v S
              (let ((D (remp
                         (lambda (d) (anyvar? d S))
                         D)))
                (rem-subsumed D))
              (remp
                (lambda (a)
                  (var? (walk (lhs a) S)))
                A)
              (remp
                (lambda (t)
                  (var? (walk (lhs t) S)))
                T))))))))

(define reify+ 
  (lambda (v S D A T)
    (let ((D (subsume A D)))
      (let ((A (map (lambda (a)
                      (let ((x (lhs a))
                            (tag (pr->tag a)))
                        `(,x . ,tag)))
                    A))
            (T (map (lambda (t)
                      (let ((x (lhs t))
                            (tag (pr->tag t)))
                        `(,x . ,tag)))
                    T)))
        (form (walk* v S)
              (walk* D S)
              (walk* A S)
              (rem-subsumed-T (walk* T S)))))))

(define form
  (lambda (v D A T)
    (let ((fd (drop-dot-D (sorter (map sorter D))))
          (fa (sorter (map sort-part (partition* A))))
          (ft (drop-dot-T (sorter T))))
      (let ((fb (append ft fa)))
        (cond
          ((and (null? fd) (null? fb)) v)
          ((null? fd) `(,v . ,fb))
          ((null? fb) `(,v . ((=/= . ,fd))))
          (else `(,v (=/= . ,fd) . ,fb)))))))

(define drop-dot-D
  (lambda (D)
    (map (lambda (d)
           (map (lambda (pr)
                  (let ((x (lhs pr))
                        (u (rhs pr)))
                    `(,x ,u)))
                d))
         D)))

(define drop-dot-T
  (lambda (T)
    (map (lambda (t)
           (let ((x (lhs t))
                 (tag (rhs t)))
             `(absent ,tag ,x)))
         T)))

(define sorter (lambda (ls) (sort lex<=? ls)))

(define sort-part
  (lambda (pr)
    (let ((tag (car pr))
          (x* (sorter (cdr pr))))
      `(,tag . ,x*))))

(define anyvar?
  (lambda (u S)
    (case-value u
      ((x) (var? (walk x S)))
      ((au du) (or (anyvar? au S)
                   (anyvar? du S)))
      ((u) #f))))

(define rem-subsumed
  (lambda (D)
    (let loop ((D D) (D+ '()))
      (cond
        ((null? D) D+)
        ((or (subsumed? (car D) (cdr D))
             (subsumed? (car D) D+))
         (loop (cdr D) D+))
        (else (loop (cdr D)
                (cons (car D) D+)))))))

(define subsumed?
  (lambda (d D)
    (cond
      ((null? D) #f)
      (else (let ((d^ (unify* (car D) d)))
              (or (and d^ (eq? d^ d))
                  (subsumed? d (cdr D))))))))

(define rem-subsumed-T
  (lambda (T)
    (let loop ((T T) (T^ '()))
      (cond
        ((null? T) T^)
        (else
         (let ((x (lhs (car T)))
               (tag (rhs (car T))))
           (cond
             ((or (subsumed-T? x tag (cdr T))
                  (subsumed-T? x tag T^))
              (loop (cdr T) T^))
             (else (loop (cdr T)
                     (cons (car T) T^))))))))))

(define subsumed-T?
  (lambda (x tag1 T)
    (cond
      ((null? T) #f)
      (else
       (let ((y (lhs (car T)))
             (tag2 (rhs (car T))))
         (or
           (and (eq? y x) (tag=? tag2 tag1))
           (subsumed-T? x tag1 (cdr T))))))))

(define unify*
  (lambda (S+ S)
    (unify (map lhs S+) (map rhs S+) S)))

(define part
  (lambda (tag A x* y*)
    (cond
     ((null? A)
      (cons `(,tag . ,x*) (partition* y*)))
     ((tag=? (rhs (car A)) tag)
      (let ((x (lhs (car A))))
        (let ((x* (cond
                    ((memq x x*) x*)
                    (else (cons x x*)))))
          (part tag (cdr A) x* y*))))
     (else
      (let ((y* (cons (car A) y*)))
        (part tag (cdr A) x* y*))))))

(define partition*
  (lambda (A)
    (cond
      ((null? A) '())
      (else
       (part (rhs (car A)) A '() '())))))

(define lex<=?
  (lambda (x y)
    (string<=? (datum->string x) (datum->string y))))

(define datum->string
  (lambda (x)
    (call-with-string-output-port
      (lambda (p) (display x p)))))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g g* ...)
     (lambdag@ (c : S D A T)
       (let ((x (walk* x S)) ...)
         ((fresh () g g* ...) c))))))

(define-syntax conda
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (ifa ((g0 c) g ...)
              ((g1 c) g^ ...) ...))))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((c-inf e))
       (case-inf c-inf
         (() (ifa b ...))
         ((f) (inc (loop (f))))
         ((a) (bind* c-inf g ...))
         ((a f) (bind* c-inf g ...)))))))

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (ifu ((g0 c) g ...)
              ((g1 c) g^ ...) ...))))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((c-inf e))
       (case-inf c-inf
         (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((c) (bind* c-inf g ...))
         ((c f) (bind* (unit c) g ...)))))))

(define onceo (lambda (g) (condu (g))))
