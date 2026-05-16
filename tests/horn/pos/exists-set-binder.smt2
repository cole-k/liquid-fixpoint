;; Regression test for elabFSetBagZ3 sort-rewriting on PExist binders.
;;
;; Before the fix, the body of `exists ((s (Set_Set int))) ...` was rewritten
;; by elabFSetBagZ3 to use `arr_*` operators on `s`, but `s` itself was left
;; annotated as `(Set_Set int)`, causing sort-checking to fail with
;;   Cannot unify (Array_t int) with Set_Set in expression: ...
;;
;; The constraint here is trivially Safe; the point is just to exercise the
;; elaborator on a PExist node with a Set_Set-typed binder + Set operators
;; in its body.

(constraint
  (forall ((x int) (true))
    (forall ((_ int) ((exists ((s (Set_Set int)))
                        (and (= s (Set_sng x))
                             (Set_mem x s)))))
      ((Set_mem x (Set_sng x))))))
