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

(declare-fun rf (Event Event) Bool)

; A read can only read from a single event
(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=> (and (rf ev1 ev2) (rf ev3 ev2))
      (= ev1 ev3))))

; Reads are paired with writes
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (rf ev1 ev2)
      (or (and (W ev1) (loc ev1 ev2) (rw-pair ev1 ev2))
          (and (= ev1 IW) (r-zero ev2))))))

; All reads read from somewhere
(assert (forall ((ev1 Event))
  (=>
    (R ev1)
    (exists ((ev2 Event)) (rf ev2 ev1)))))
