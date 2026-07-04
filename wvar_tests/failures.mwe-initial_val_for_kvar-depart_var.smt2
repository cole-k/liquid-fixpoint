;; Tag 0: Ret at 112:9: 112:10 (ESpan { span: benchmarks/failures/src/mwe.rs:93:47: 93:52 (#0), base: None })

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
(var $k0 (int int int int)) ;; orig: $k1
(var $k1 (int int int)) ;; orig: $k1
(var $k2 (int int int int int int)) ;; orig: $k0
(wvar $wk$mwe__initial_val_for_kvar__depart_var$0 (int int))  ;; weak kvar: WKVid { parent_fn: DefId(0:37 ~ failures[7370]::mwe::initial_val_for_kvar::depart_var), id: $k0 }
(wvar $wk$mwe__initial_val_for_kvar__mk_usize$1 (int ))  ;; weak kvar: WKVid { parent_fn: DefId(0:18 ~ failures[7370]::mwe::initial_val_for_kvar::mk_usize), id: $k1 }

(constraint
 (forall ((reftgen$m$0 int) (true))
  (forall ((reftgen$i0$1 int) (true))
     (forall ((_$ int) ($wk$mwe__initial_val_for_kvar__depart_var$0 reftgen$m$0 reftgen$i0$1))
    (forall ((_invariant$ int) ((>= reftgen$m$0 0)))
     (forall ((_invariant$ int) ((>= reftgen$i0$1 0)))
      (and
       (and
        ($k0 reftgen$i0$1 reftgen$i0$1 reftgen$m$0 reftgen$i0$1)
        ($k1 reftgen$i0$1 reftgen$m$0 reftgen$i0$1))
       (forall ((a0 int) (true))
        (forall ((a1 int) (true))
         (forall ((_$ int) (and ($k0 a0 a1 reftgen$m$0 reftgen$i0$1) ($k1 a1 reftgen$m$0 reftgen$i0$1)))
          (and
           (forall ((_$ int) ((not (< a1 reftgen$m$0))))
            (and
             (true)
             (tag ((< a0 reftgen$m$0)) "0")))
           (forall ((_$ int) ((< a1 reftgen$m$0)))
            (and
             (true)
             (forall ((a2 int) (true))
               (forall ((_$ int) ($wk$mwe__initial_val_for_kvar__mk_usize$1 a2))
               (forall ((_invariant$ int) ((>= a2 0)))
                (and
                 (forall ((_$ int) ((not (< 0 a2))))
                  ($k2 a0 reftgen$m$0 reftgen$i0$1 a0 a1 a2))
                 (forall ((_$ int) ((< 0 a2)))
                  ($k2 a1 reftgen$m$0 reftgen$i0$1 a0 a1 a2))
                 (forall ((a3 int) (true))
                  (forall ((_$ int) ($k2 a3 reftgen$m$0 reftgen$i0$1 a0 a1 a2))
                   (forall ((a4 int) ((= a4 (+ a1 1))))
                    (and
                     ($k0 a3 a4 reftgen$m$0 reftgen$i0$1)
                     ($k1 a4 reftgen$m$0 reftgen$i0$1))))))))))))))))))))))

