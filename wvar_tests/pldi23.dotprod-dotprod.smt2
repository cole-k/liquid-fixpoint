;; Tag 0: Call at 15:20: 15:23 (ESpan { span: benchmarks/pldi23/src/vec.rs:26:57: 26:66 (#0), base: None })

(datatype (Adt0 0) ((mkadt0$0 ((fld0$0 int)))))
(qualif EqTrue ((a0 bool)) (a0))
(qualif EqFalse ((a0 bool)) ((not a0)))
(qualif EqZero ((a0 int)) ((= a0 0)))
(qualif GtZero ((a0 int)) ((> a0 0)))
(qualif GeZero ((a0 int)) ((>= a0 0)))
(qualif LtZero ((a0 int)) ((< a0 0)))
(qualif LeZero ((a0 int)) ((<= a0 0)))
(qualif Eq ((a0 int) (a1 int)) ((= a0 a1)))
(qualif Gt ((a0 int) (a1 int)) ((> a0 a1)))
(qualif Ge ((a0 int) (a1 int)) ((>= a0 a1)))
(qualif Lt ((a0 int) (a1 int)) ((< a0 a1)))
(qualif Le ((a0 int) (a1 int)) ((<= a0 a1)))
(qualif Le1 ((a0 int) (a1 int)) ((<= a0 (- a1 1))))
(constant gt (func 1 (@(0) @(0) ) bool))
(constant ge (func 1 (@(0) @(0) ) bool))
(constant lt (func 1 (@(0) @(0) ) bool))
(constant le (func 1 (@(0) @(0) ) bool))
(var $k0 (int int int int)) ;; orig: $k0
(var $k1 (int int int)) ;; orig: $k0
(wvar $wk$dotprod__dotprod$0 ((Adt0) (Adt0)))  ;; weak kvar: WKVid { parent_fn: DefId(0:4 ~ pldi23[3b0e]::dotprod::dotprod), id: $k0 }

(constraint
 (forall ((reftgen$n$0 (Adt0)) (true))
  (forall ((reftgen$m$1 (Adt0)) (true))
    (forall ((_$ int) ($wk$dotprod__dotprod$0 reftgen$n$0 reftgen$m$1))
    (forall ((_invariant$ int) ((>= (fld0$0 reftgen$n$0) 0)))
     (and
      (forall ((a0 int) ((= a0 0)))
       (forall ((a1 int) ((= a1 0)))
        (forall ((a2 int) ((= a2 (fld0$0 reftgen$n$0))))
         (forall ((a3 int) ((= a3 (fld0$0 reftgen$m$1))))
          (and
           ($k0 a0 a1 a2 a3)
           ($k1 a1 a2 a3))))))
      (forall ((a4 int) (true))
       (forall ((a5 int) (true))
        (forall ((a6 int) ((= a6 (fld0$0 reftgen$n$0))))
         (forall ((a7 int) ((= a7 (fld0$0 reftgen$m$1))))
          (forall ((_$ int) (and ($k0 a4 a5 a6 a7) ($k1 a5 a6 a7)))
           (and
            (forall ((_$ int) ((not (< a4 (fld0$0 reftgen$n$0)))))
             (true))
            (forall ((_$ int) ((< a4 (fld0$0 reftgen$n$0))))
             (forall ((a8 int) (true))
              (and
               (tag ((< a4 (fld0$0 reftgen$m$1))) "0")
               (forall ((a9 int) (true))
                (forall ((a10 int) ((= a10 (+ a4 1))))
                 (forall ((a11 int) ((= a11 (+ a5 (* a8 a9)))))
                  (forall ((a12 int) ((= a12 (fld0$0 reftgen$n$0))))
                   (forall ((a13 int) ((= a13 (fld0$0 reftgen$m$1))))
                    (and
                     ($k0 a10 a11 a12 a13)
                     ($k1 a11 a12 a13))))))))))))))))))))))

