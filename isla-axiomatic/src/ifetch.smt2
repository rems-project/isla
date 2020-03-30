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

(declare-fun scl (Event Event) Bool)

(assert (forall ((ev1 Event) (ev2 Event))
  (= (scl ev1 ev2)
     (= (addr_of ev1) (addr_of ev2)))))