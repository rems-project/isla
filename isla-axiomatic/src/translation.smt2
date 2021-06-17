
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

; write-ordered-by-translate
(define-fun wot ((ev1 Event) (ev2 Event)) Bool
   (exists ((ev3 Event)) (translated_before ev3 (addr_of ev1) (addr_of ev2))))

(define-fun tlbi_va ((addr (_ BitVec 64))) (_ BitVec 64)
   (concat #x00 ((_ extract 43 0) addr) #x000))

; TODO: Check this
(define-fun tlbi_ipa ((addr (_ BitVec 64))) (_ BitVec 64)
   (concat #x00 ((_ extract 43 0) addr) #x000))

(define-fun tlbi-same-va-page ((ev1 Event) (ev2 Event)) Bool
   (and (T ev1) (TLBI-VA ev2) (= (translate_va ev1) (tlbi_va (val_of_cache_op ev2)))))

(define-fun tlbi-same-ipa-page ((ev1 Event) (ev2 Event)) Bool
   (and (T ev1) (TLBI-IPA ev2) (= (translate_ipa ev1) (tlbi_ipa (val_of_cache_op ev2)))))

(define-fun same-va-page ((ev1 Event) (ev2 Event)) Bool
   (or (translate-same-va-page ev1 ev2)
       (tlbi-same-va-page ev1 ev2)
       (tlbi-same-va-page ev2 ev1)))

(define-fun same-ipa-page ((ev1 Event) (ev2 Event)) Bool
   (or (translate-same-ipa-page ev1 ev2)
       (tlbi-same-ipa-page ev1 ev2)
       (tlbi-same-ipa-page ev2 ev1)))
