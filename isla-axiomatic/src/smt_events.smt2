
;
; CO
;

(declare-fun co (Event Event) Bool)

; co is irreflexive
(assert (forall ((ev Event))
  (not (co ev ev))))

; co is transitive
(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=>
    (and (co ev1 ev2) (co ev2 ev3))
    (co ev1 ev3))))

; Two distinct writes to the same location are co-related
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (W ev1)
         (W ev2)
         (loc ev1 ev2))
    (or (co ev1 ev2) (co ev2 ev1)))))

; All writes are coherence order after the initial write
(assert (forall ((ev Event))
  (=> (W ev) (co IW ev))))

; All co-ordered writes must be to the same location if not the initial write
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (and (not (= ev1 IW)) (co ev1 ev2)) (loc ev1 ev2))))

; co is total
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (exists ((ev3 Event))
           (and (co ev1 ev3)
                (co ev2 ev3))))
    (or (co ev1 ev2) (co ev2 ev1)))))

; All co-ordered events are writes
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (co ev1 ev2)
    (and (or (= ev1 IW) (W ev1)) (W ev2)))))


;
; RF
;

(declare-fun rf (Event Event) Bool)

; A read can only read from a single event
(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=> (and (rf ev1 ev2) (rf ev3 ev2))
      (= ev1 ev3))))

; Reads are paired with writes
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (rf ev1 ev2)
      (or (and (W ev1) (loc ev1 ev2) (rw-pair ev1 ev2))
          (and (= ev1 IW) (r-initial ev2))))))

; All reads read from somewhere
(assert (forall ((ev1 Event))
  (=>
    (R ev1)
    (exists ((ev2 Event)) (rf ev2 ev1)))))

;
; WCO
;

(declare-fun wco (Event Event) Bool)

; wco is irreflexive
(assert (forall ((ev Event))
  (not (wco ev ev))))

; wco is transitive
(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=>
    (and (wco ev1 ev2) (wco ev2 ev3))
    (wco ev1 ev3))))

; wco is total
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (exists ((ev3 Event))
           (and (wco ev1 ev3)
                (wco ev2 ev3))))
    (or (wco ev1 ev2) (wco ev2 ev1)))))

; distinct writes to the same location are wco-related
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (W ev1)
         (W ev2)
         (loc ev1 ev2))
    (or (wco ev1 ev2) (wco ev2 ev1)))))

; wco relates writes and cache ops
(assert (forall ((ev1 Event) (ev2 Event))
  (=>
     (wco ev1 ev2)
     (and (or (= ev1 IW) (W ev1) (C ev1))
          (or (W ev2) (C ev2))))))

; wco is consistent with co
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (co ev1 ev2) (wco ev1 ev2))))

; All cache-operations and writes are wco after the initial write
(assert (forall ((ev Event))
  (=> (or (W ev) (C ev)) (wco IW ev))))