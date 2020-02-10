(declare-fun co (Event Event) Bool)

(assert (forall ((ev Event))
  (not (co ev ev))))

(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=>
    (and (co ev1 ev2) (co ev2 ev3))
    (co ev1 ev3))))

(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (not (= ev1 ev2))
         (W ev1)
         (W ev2)
         (loc ev1 ev2))
    (or (co ev1 ev2) (co ev2 ev1)))))

(assert (forall ((ev1 Event) (ev2 Event))
  (=>
    (and (= ev1 IW)
         (W ev2)
         (not (exists ((ev3 Event)) (co ev3 ev2))))
    (co ev1 ev2))))

(declare-fun rf (Event Event) Bool)

(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
  (=> (and (rf ev1 ev2) (rf ev3 ev2))
      (= ev1 ev3))))

(assert (forall ((ev1 Event) (ev2 Event))
  (=> (rf ev1 ev2)
      (or (and (W ev1) (loc ev1 ev2) (rw-pair ev1 ev2))
          (and (= ev1 IW) (r-zero ev2))))))

(assert (forall ((ev1 Event))
  (=>
    (R ev1)
    (exists ((ev2 Event)) (rf ev2 ev1)))))
