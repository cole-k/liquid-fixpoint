;; Tag 0: Call at 160:13: 160:28

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
(wvar $wk$mwe__wkvar_kvar_interaction__simplex$0 (int))  ;; weak kvar: WKVid { parent_fn: DefId(0:40 ~ failures[7370]::mwe::wkvar_kvar_interaction::simplex), id: $k0 }
(var $k0 (int int)) ;; orig: $k0

(constraint
 (forall ((reftgen$m$0 int) (true))
  (forall ((_$ int) ($wk$mwe__wkvar_kvar_interaction__simplex$0 reftgen$m$0))
   (forall ((_invariant$ int) ((>= reftgen$m$0 0)))
    (forall ((_invariant$ int) (true))
     (and
      ($k0 reftgen$m$0 reftgen$m$0)
      (forall ((a0 int) (true))
       (forall ((_$ int) ($k0 a0 reftgen$m$0))
        (and
         (true)
         (tag ((= a0 reftgen$m$0)) "0")
         (forall ((a1 int) (true))
          (forall ((_invariant$ int) ((>= a1 0)))
           ($k0 a1 reftgen$m$0))))))))))))

