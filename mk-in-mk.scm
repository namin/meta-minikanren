(define orig-minus -)

(define (- var const out)
  (lambdag@ (st)
    ((== (orig-minus (walk var (state-S st)) const) out) st)))

(define orig-plus +)

(define (+ var const out)
  (lambdag@ (st)
    ((== (orig-plus (walk var (state-S st)) const) out) st)))


(define (varo v)
  (numbero v))

(define (pairo v)
  (fresh (a d)
    (== `(,a . ,d) v)))

(define (nullo v)
  (== v '()))

(define (atomico v)
  (conde
    [(nullo v)]
    [(symbolo v)]))

(define (not-varo v)
  (conde
    [(atomico v)]
    [(pairo v)]))

(define (lookupo u s out)
  (conde
    [(== s '())
     (== out #f)]
    [(fresh (key val rest)
       (== `((,key . ,val) . ,rest) s)
       (conde
         [(== u key)
          (== val out)]
         [(=/= u key)
          (lookupo u rest out)]))]))

(define (walko u s out)
  (fresh (res)
    (conde
      [(not-varo u)
       (== res #f)]
      [(varo u)
       (lookupo u s res)])
    (conde
      [(== res #f)
       (== u out)]
      [(=/= res #f)
       (walko res s out)])))

(define (occurs-checko x v-in s out)
  (fresh (v)
    (walko v-in s v)
    (conde
      [(varo v)
       (conde
         [(== x v)
          (== out #t)]
         [(=/= x v)
          (== out #f)])]
      [(fresh (va vd res)
         (== `(,va . ,vd) v)
         (occurs-checko x va s res)
         (conde
           [(== res #t)
            (== out #t)]
           [(== res #f)
            (occurs-checko x vd s out)]))]
      [(atomico v)
       (== out #f)])))

(define (ext-s-checko x v s out)
  (fresh (res)
    (occurs-checko x v s res)
    (conde
      [(== res #t) (== out #f)]
      [(== res #f) (== `((,x . ,v) . ,s) out)])))

(define (unifyo u-in v-in s out)
  (fresh (u v)
    (walko u-in s u)
    (walko v-in s v)
    (conde
      [(varo u)
       (varo v)
       (== u v)
       (== s out)]
      [(varo u)
       (conde
         [(not-varo v)]
         [(varo v)
          (=/= u v)])
       (ext-s-checko u v s out)]
      [(varo v)
       (not-varo u)
       (ext-s-checko v u s out)]
      [(fresh (ua ud va vd s^)
         (== `(,ua . ,ud) u)
         (== `(,va . ,vd) v)
         (unifyo ua va s s^)
         (conde
           [(== s^ #f)
            (== out #f)]
           [(=/= s^ #f)
            (unifyo ud vd s^ out)]))]
      [(atomico u)
       (pairo v)
       (== out #f)]
      [(pairo u)
       (atomico v)
       (== out #f)]
      [(atomico u)
       (atomico v)
       (conde
         [(== u v)
          (== out s)]
         [(=/= u v)
          (== out #f)])])))

(define (atomic-evalo exp env out)
  (conde
    [(symbolo exp)
     (=/= out #f)
     (lookupo exp env out)]
    [(fresh (quoted)
       (== `(quote ,quoted) exp)
       (conde
         [(symbolo quoted)]
         [(nullo quoted)])
       (== out quoted))]
    [(fresh (le re lv rv)
       (== `(cons ,le ,re) exp)
       (== `(,lv . ,rv) out)
       (atomic-evalo le env lv)
       (atomic-evalo re env rv))]))

(define fail `(inc-k (== 'a 'b) () () 0 ()))

(define (atomic-eval-listo in env out)
  (conde
    [(== in '())
     (== out '())]
    [(fresh (a av d res)
       (== `(,a . ,d) in)
       (== `(,av . ,res) out)
       (atomic-evalo a env av)
       (atomic-eval-listo d env res))]))

(define (ext-env*o x* a* env out)
  (conde
    ((== '() x*) (== '() a*) (== env out))
    ((fresh (x a dx* da* env2)
       (== `(,x . ,dx*) x*)
       (== `(,a . ,da*) a*)
       (== `((,x . ,a) . ,env) env2)
       (symbolo x)
       (ext-env*o dx* da* env2 out)))))

(define (step-evalo exp env genv ctr subst context out)
  (conde
    [(fresh (name args argvs params body new-env)
       (== `(,name . ,args) exp)
       (atomic-eval-listo args env argvs)
       (lookupo name genv `(goal ,params ,body))
       (ext-env*o params argvs '() new-env)
       (step-evalo body new-env genv ctr subst context out))]
    [(fresh (le re lv rv res)
       (== `(== ,le ,re) exp)
       (atomic-evalo le env lv)
       (atomic-evalo re env rv)
       (unifyo lv rv subst res)
       (conde
         [(== res #f)
          (fail-ko context out)]
         [(=/= res #f)
          (success-ko ctr res fail context out)]))]
    [(fresh (var body ctr^)
       (== `(fresh ,var ,body) exp)
       (+ ctr 1 ctr^)
       (step-evalo body `((,var . ,ctr^) . ,env) genv ctr^ subst context out))]
    [(fresh (l r)
       (== `(disj ,l ,r) exp)
       (step-evalo l env genv ctr subst `(mplus-context (inc-k ,r ,env ,genv ,ctr ,subst) ,context) out))]
    [(fresh (l r)
       (== `(conj ,l ,r) exp)
       (step-evalo l env genv ctr subst `(bind-context (goal-k ,r ,env ,genv) ,context) out))]))

(define (step-searcho tree context out)
  (conde
    [(fresh (left right)
       (== `(mplus ,left ,right) tree)
       (step-searcho left `(mplus-context ,right ,context) out))]
    [(fresh (tree^ goal)
       (== `(bind ,tree^ ,goal) tree)
       (step-searcho tree^ `(bind-context ,goal ,context) out))]
    [(fresh (exp env genv subst ctr)
       (== `(inc-k ,exp ,env ,genv ,ctr ,subst) tree)
       (step-evalo exp env genv ctr subst context out))]))

(define (fail-ko context out)
  (conde
    [(fresh (goal parent)
       (== `(bind-context ,goal ,parent) context)
       (fail-ko parent out))]
    [(fresh (right parent)
       (== `(mplus-context ,right ,parent) context)
       (step-searcho right parent out))]
    [(== `(top-context) context)
     (== `(failure) out)]))

(define (success-ko ctr subst remaining-tree context out)
  (conde
    [(fresh (exp env genv parent)
       (== `(bind-context (goal-k ,exp ,env ,genv) ,parent) context)
       (step-searcho `(mplus (inc-k ,exp ,env ,genv ,ctr ,subst) (bind ,remaining-tree (goal-k ,exp ,env ,genv))) parent out))]
    [(fresh (right parent)
       (== `(mplus-context ,right ,parent) context)
       (success-ko ctr subst `(mplus ,right ,remaining-tree) parent out))]
    [(== `(top-context) context)
     (== `(success ,subst ,remaining-tree) out)]))

(define (walk*o v-arg s res)
  (fresh (v)
    (walko v-arg s v)
    (conde
      [(varo v) (== res v)]
      [(atomico v) (== res v)]
      [(fresh (a d ar dr)
         (== `(,a . ,d) v)
         (== `(,ar . ,dr) res)
         (walk*o a s ar)
         (walk*o d s dr))])))

(define (drivero n tree out)
  (conde
    [(== n 0) (== out '())]
    [(fresh (res)
       (=/= n 0)
       (step-searcho tree '(top-context) res)
       (conde
         [(== res '(failure))
          (== out '())]
         [(fresh (s new-tree n^ res2 reified-lvar)
            (== `(success ,s ,new-tree) res)
            (== `(,reified-lvar . ,res2) out)
            (- n 1 n^)
            (walk*o 0 s reified-lvar)
            (drivero n^ new-tree res2))]))]))

(define (list-of-symbolso los)
  (conde
    ((== '() los))
    ((fresh (a d)
       (== `(,a . ,d) los)
       (symbolo a)
       (list-of-symbolso d)))))

(define (process-defso defs genv)
  (conde
    [(== defs '())
     (== genv '())]
    [(fresh (name args body rest res)
       (== `((define (,name . ,args) ,body) . ,rest) defs)
       (== `((,name . (goal ,args ,body)) . ,res) genv)
       (symbolo name)
       (=/= name 'fresh)
       (=/= name 'disj)
       (=/= name 'conj)
       (=/= name '==)
       (list-of-symbolso args)
       (process-defso rest res))]))

(define (eval-mko program out)
  (fresh (n lvar defs goal genv)
    (== `((begin . ,defs) (run ,n (,lvar) ,goal)) program)
    (process-defso defs genv)
    (symbolo lvar)
    (drivero n `(inc-k ,goal ((,lvar . 0)) ,genv 1 ()) out)))


