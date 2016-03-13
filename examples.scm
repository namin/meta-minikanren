(run 1 (q)
     (eval-mko
       `((begin
           (define (appendo l s out)
             (disj
               (conj
                 (== l '())
                 (== s out))
               (fresh a
                 (fresh d
                   (fresh res
                     (conj
                       (conj
                         (== (cons a d) l)
                         (== (cons a res) out))
                       (appendo d s res)))))))
           )
         (run 1 (q) (appendo (cons 'a (cons 'b '())) (cons 'c '()) q)))
       q))

(run 1 (q)
     (eval-mko
       `((begin
           (define (appendo l s out)
             (disj
               (conj
                 (== l '())
                 (== s out))
               (fresh a
                 (fresh d
                   (fresh res
                     (conj
                       (conj
                         (== (cons a d) l)
                         (== (cons a res) out))
                       (appendo d s res)))))))
           )
         (run 1 (q) (appendo q (cons 'c '()) (cons 'a (cons 'b (cons 'c '()))))))
       q))

(run 1 (q)
     (eval-mko
       `((begin
           (define (appendo l s out)
             (disj
               (conj
                 (== l '())
                 (== s out))
               (fresh a
                 (fresh d
                   (fresh res
                     (conj
                       (conj
                         (== (cons a d) l)
                         (== (cons a res) out))
                       (appendo d s res)))))))
           )
         (run 6 (q) (fresh x
                      (fresh y
                        (conj (== (cons x (cons y '())) q)
                              (appendo x y (cons 'a (cons 'b (cons 'c '())))))))))
       q))

(run 1 (q)
     (eval-mko
       `((begin
           (define (appendo l s out)
             (disj
               (conj
                 (== l '())
                 (== s out))
               (fresh a
                 (fresh d
                   (fresh res
                     (conj
                       (conj
                         (== (cons a d) l)
                         (== (cons a res) out))
                       (appendo d s res)))))))
           )
         (run 7 (q) (fresh x
                      (fresh y
                        (conj (== (cons x (cons y '())) q)
                              (appendo x y (cons 'a (cons 'b (cons 'c '())))))))))
       q))

(run 11 (q)
     (fresh (res)
       (=/= res '())
       (eval-mko
         `((begin
             (define (appendo l s out)
               (disj
                 (conj
                   (== l '())
                   (== s out))
                 (fresh a
                   (fresh d
                     (fresh res
                       (conj
                         (conj
                           (== (cons a d) l)
                           (== (cons a res) out))
                         (appendo d s res)))))))
             )
           (run 1 (q) (appendo ,q (cons 'c '()) (cons 'a (cons 'b (cons 'c '()))))))
         res)))


(run 10 (q)
     (fresh (res)
       (=/= res '())
       (eval-mko
         `((begin
             (define (appendo l s out)
               (disj
                 (conj
                   (== l '())
                   (== s out))
                 (fresh a
                   (fresh d
                     (fresh res
                       (conj
                         (conj
                           (== (cons a d) l)
                           (== (cons a res) out))
                         (appendo d s res)))))))
             )
           (run 1 (q) (appendo ,q (cons 'c '()) (cons 'a (cons 'b (cons 'c '()))))))
         res)))
;=>
;q
;(cons 'a q)
;(cons 'a q)
;(cons q (cons 'b '()))
;(cons q (cons 'b '()))
;(cons 'a (cons q '()))
;(cons 'a (cons q '()))
;(cons 'a (cons 'b q))
;(cons 'a (cons 'b q))
;(cons 'a (cons 'b '()))
;
;Note the duplicate answers.



(run 10 (q res)
     (fresh ()
       (=/= res '())
       (eval-mko
         `((begin
             (define (appendo l s out)
               (disj
                 (conj
                   (== l '())
                   (== s out))
                 (fresh a
                   (fresh d
                     (fresh res
                       (conj
                         (conj
                           (== (cons a d) l)
                           (== (cons a res) out))
                         (appendo d s res)))))))
             )
           (run 1 (q) (appendo ,q (cons 'c '()) (cons 'a (cons 'b (cons 'c '()))))))
         res)))

(q ((a b)))
((cons 'a q) ((b)))
((cons 'a q) ((b)))
((cons q (cons 'b '())) (a))
((cons q (cons 'b '())) (a))
((cons 'a (cons q '())) (b))
((cons 'a (cons q '())) (b))
((cons 'a (cons 'b q)) (()))
((cons 'a (cons 'b q)) (()))
((cons 'a (cons 'b '())) (0))


; can't use multiple appendo calls within the nested run to help synthesis, as each
; can only require that appendo succeed. To assert that appendo must fail, we need
; multiple run calls. because of how our evaluator is set up, that means multiple
; eval-mko calls.
(run 1 (q)
     (fresh (code res1 single-ans1 res2 single-ans2)
       (== code
           `(begin
              (define (appendo l s out)
                (disj
                  (conj
                    (== l '())
                    (== s out))
                  (fresh a
                    (fresh d
                      (fresh res
                        (conj
                          (conj
                            (== (cons a d) l)
                            (== (cons a res) out))
                          (appendo d s res)))))))
              ))

       (== res2 `(,single-ans2))
       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   '()
                   (cons 'c '())
                   (cons 'c '()))))
         res2)

       (== res1 `(,single-ans1))
       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   (cons 'a (cons 'b '()))
                   (cons 'c '())
                   (cons 'a (cons 'b (cons 'c '()))))))
         res1)))


(run 1 (q)
     (fresh (code res1 single-ans1 res2 single-ans2)
       (== code
           `(begin
              (define (appendo l s out)
                (disj
                  (== s out)
                  (fresh a
                    (fresh d
                      (fresh res
                        (conj
                          (conj
                            (== (cons a d) l)
                            (== (cons a res) out))
                          (appendo d s res)))))))
              ))

       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   (cons 'a '())
                   q
                   (cons 'a '()))))
         q)))



(run 2 (q)
     (fresh (code res1 single-ans1 res2 single-ans2)
       (== code
           `(begin
              (define (appendo l s out)
                (disj
                  (conj
                    (== ,q '())
                    (== s out))
                  (fresh a
                    (fresh d
                      (fresh res
                        (conj
                          (conj
                            (== (cons a d) l)
                            (== (cons a res) out))
                          (appendo d s res)))))))
              ))

       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   q
                   (cons 'c '())
                   (cons 'c '()))))
         '(()))

       (== res1 `(,single-ans1))
       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   (cons 'a (cons 'b '()))
                   (cons 'c '())
                   (cons 'a (cons 'b (cons 'c '()))))))
         res1)))


(run 1 (q)
     ;(== q '(d s res))
     (fresh (code res1 single-ans1 res2 single-ans2)
       (== code
           `(begin
              (define (appendo l s out)
                (disj
                  (conj
                    (== l '())
                    (== s out))
                  (fresh a
                    (fresh d
                      (fresh res
                        (conj
                          (conj
                            (== (cons a d) l)
                            (== (cons a res) out))
                          (appendo . ,q)))))))
              ))

       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   q
                   (cons 'c '())
                   (cons 'c '()))))
         '(()))

       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   (cons 'a (cons 'b '()))
                   (cons 'c '())
                   (cons 'b (cons 'b (cons 'c '()))))))
         '())

       (== res2 `(,single-ans2))
       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   (cons 'b (cons 'c '()))
                   (cons 'd '())
                   (cons 'b (cons 'c (cons 'd '()))))))
         res2)

       (== res1 `(,single-ans1))
       (eval-mko
         `(,code
            (run 2 (q)
                 (appendo
                   (cons 'a (cons 'b '()))
                   (cons 'c '())
                   (cons 'a (cons 'b (cons 'c '()))))))
         res1)))

