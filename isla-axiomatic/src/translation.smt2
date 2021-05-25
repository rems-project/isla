
; A write of a valid descriptor (an odd value) is a member of W_valid
(define-fun W_valid ((ev Event)) Bool
   (= (bvand (val_of_64 ev) #x0000000000000001) #x0000000000000001))

; A write of an invalid descriptor (an even value) is a member of W_invalid
(define-fun W_invalid ((ev Event)) Bool
   (= (bvand (val_of_64 ev) #x0000000000000001) #x0000000000000000))

; Translation reads-from (trf) and stage 1 and stage 2 specific variants
(declare-fun trf1 (Event Event) Bool)
(declare-fun trf2 (Event Event) Bool)
(declare-fun trf (Event Event) Bool)
(assert (forall ((ev1 Event) (ev2 Event)) (= (trf1 ev1 ev2) (trf1-internal ev1 ev2))))
(assert (forall ((ev1 Event) (ev2 Event)) (= (trf2 ev1 ev2) (trf2-internal ev1 ev2))))
(assert (forall ((ev1 Event) (ev2 Event)) (= (trf ev1 ev2) (or (trf1-internal ev1 ev2) (trf2-internal ev1 ev2)))))

(define-fun wot ((ev1 Event) (ev2 Event)) Bool
   (exists ((ev3 Event)) (translated_before ev3 (addr_of ev1) (addr_of ev2))))
