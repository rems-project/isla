(declare-fun irf (Event Event) Bool)

; A fetch can only read from a single event
(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=> (and (irf ev1 ev2) (irf ev3 ev2))
      (= ev1 ev3))))

; Fetches are paired with writes
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (irf ev1 ev2)
      (or (and (W ev1) (loc ev1 ev2) (ifetch-match ev2) (rw-pair ev1 ev2))
          (and (= ev1 IW) (ifetch-initial ev2))))))

; All fetches read from somewhere
(assert (forall ((ev1 Event))
  (=>
    (IF ev1)
    (exists ((ev2 Event)) (irf ev2 ev1)))))

(define-fun scl ((ev1 Event) (ev2 Event)) Bool
  (loc ev1 ev2))

(declare-fun wco (Event Event) Bool)

; wco is irreflexive
(assert (forall ((ev Event))
  (not (wco ev ev))))

; wco is transitive
(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=>
    (and (wco ev1 ev2) (wco ev2 ev3))
    (wco ev1 ev3))))

; Two distinct writes to the same location are wco-related
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (W ev1)
         (W ev2)
         (loc ev1 ev2))
    (or (wco ev1 ev2) (wco ev2 ev1)))))

; Cache operations and writes/other cache operations to the same cache-line are wco-related
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (C ev1)
         (or (W ev2) (C ev2))
         (scl ev1 ev2))
    (or (wco ev1 ev2) (wco ev2 ev1)))))

; All cache-operations and writes are wco after the initial write
(assert (forall ((ev Event))
  (=> (or (W ev) (C ev)) (wco IW ev))))

; All wco-ordered events must be to the same cache line if not the initial write
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (and (not (= ev1 IW)) (wco ev1 ev2)) (scl ev1 ev2))))

; wco is total
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (exists ((ev3 Event))
           (and (wco ev1 ev3)
                (wco ev2 ev3))))
    (or (wco ev1 ev2) (wco ev2 ev1)))))

; All wco-ordered events are writes or cache ops
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (wco ev1 ev2)
    (and (or (= ev1 IW) (W ev1) (C ev1))
         (or (W ev2) (C ev2))))))

; wco is consistent with co
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (co ev1 ev2) (wco ev1 ev2))))
