; A write of a valid descriptor (an odd value) is a member of W_valid
(define-fun W_valid ((ev Event)) Bool
   (= (bvand (val_of_64 ev) #x0000000000000001) #x0000000000000001))

; A write of an invalid descriptor (an even value) is a member of W_invalid
(define-fun W_invalid ((ev Event)) Bool
   (= (bvand (val_of_64 ev) #x0000000000000001) #x0000000000000000))

(define-fun is_IW ((ev Event)) Bool
   (= ev IW))

; Translation reads-from (trf) and stage 1 and stage 2 specific variants
(declare-fun trf1 (Event Event) Bool)
(declare-fun trf2 (Event Event) Bool)
(declare-fun trf (Event Event) Bool)
(assert (forall ((ev1 Event) (ev2 Event)) (= (trf1 ev1 ev2) (trf1-internal ev1 ev2))))
(assert (forall ((ev1 Event) (ev2 Event)) (= (trf2 ev1 ev2) (trf2-internal ev1 ev2))))
(assert (forall ((ev1 Event) (ev2 Event)) (= (trf ev1 ev2) (or (trf1-internal ev1 ev2) (trf2-internal ev1 ev2)))))

; A translation-read can only read from a single event
;(assert (forall ((ev1 Event) (ev2 Event) (ev3 Event))
;  (=> (and (trf ev1 ev2) (trf ev3 ev2))
;      (= ev1 ev3))))

; Translation-reads are paired with writes
;(assert (forall ((ev1 Event) (ev2 Event))
;  (=> (trf ev1 ev2)
;      (or (and (W ev1) (loc ev1 ev2) (rw-pair ev1 ev2))
;          (and (= ev1 IW) (r-initial ev2))))))

; All translations read from at least one write
(assert (forall ((ev1 Event))
  (=>
    (T ev1)
    (exists ((ev2 Event)) (trf ev2 ev1)))))

; write-ordered-by-translate
(define-fun wot ((ev1 Event) (ev2 Event)) Bool
  (exists ((ev3 Event)) (translated_before ev3 (addr_of ev1) (addr_of ev2))))

(define-fun tlbi_va ((data (_ BitVec 64))) (_ BitVec 64)
  (concat #x00 ((_ extract 43 0) data) #x000))

(define-fun tlbi_asid ((data (_ BitVec 64))) (_ BitVec 16)
  ((_ extract 63 48) data))

(declare-fun same-asid-internal (Event Event) Bool)
(assert (forall ((ev1 Event) (ev2 Event))
  (= (same-asid-internal ev1 ev2)
     (and (not (= ev1 ev2))
       (or
         (and (TLBI-ASID ev1) (AT ev2) (read_ASID ev2) (= (tlbi_asid (val_of_cache_op ev1)) (tlbi_asid (val_of_read_ASID ev2))))
         (and (TLBI-ASID ev2) (AT ev1) (read_ASID ev1) (= (tlbi_asid (val_of_cache_op ev2)) (tlbi_asid (val_of_read_ASID ev1))))
         (and (TLBI-ASID ev1) (TLBI-ASID ev2) (= (tlbi_asid (val_of_cache_op ev1)) (tlbi_asid (val_of_cache_op ev2))))
         (and (AT ev1) (read_ASID ev1) (AT ev2) (read_ASID ev2) (= (tlbi_asid (val_of_read_ASID ev1)) (tlbi_asid (val_of_read_ASID ev2)))))))))

(define-fun tlbi-to-asid-read ((ev1 Event) (ev2 Event)) Bool
  (and (TLBI-ASID ev1) (AT ev2) (read_ASID ev2) (= (tlbi_asid (val_of_cache_op ev1)) (tlbi_asid (val_of_read_ASID ev2)))))

(define-fun tlbi_vmid ((data (_ BitVec 64))) (_ BitVec 16)
  ((_ extract 15 0) data))

(define-fun reg_vmid ((data (_ BitVec 64))) (_ BitVec 16)
  ((_ extract 63 48) data))

(declare-fun same-vmid-internal (Event Event) Bool)
(assert (forall ((ev1 Event) (ev2 Event))
  (= (same-vmid-internal ev1 ev2)
     (and
      (not (= ev1 ev2))
      (or
        (and (TLBI-VMID ev1) (AT ev2) (read_VMID ev2) (= (tlbi_vmid (val_of_cache_op_extra ev1)) (reg_vmid (val_of_read_VMID ev2))))
        (and (TLBI-VMID ev2) (AT ev1) (read_VMID ev1) (= (tlbi_vmid (val_of_cache_op_extra ev2)) (reg_vmid (val_of_read_VMID ev1))))
        (and (TLBI-VMID ev1) (TLBI-VMID ev2) (= (tlbi_vmid (val_of_cache_op_extra ev1)) (tlbi_vmid (val_of_cache_op_extra ev2))))
        (and (AT ev1) (read_VMID ev1) (AT ev2) (read_VMID ev2) (= (reg_vmid (val_of_read_VMID ev1)) (reg_vmid (val_of_read_VMID ev2)))))))))

(define-fun tlbi-to-vmid-read ((ev1 Event) (ev2 Event)) Bool
  (and (TLBI-VMID ev1) (AT ev2) (read_VMID ev2) (= (tlbi_vmid (val_of_cache_op_extra ev1)) (reg_vmid (val_of_read_VMID ev2)))))

; TODO: Check this
(define-fun tlbi_ipa ((addr (_ BitVec 64))) (_ BitVec 64)
  (concat #x00 ((_ extract 43 0) addr) #x000))

(declare-fun tlbi-same-va-page (Event Event) Bool)
(assert
   (forall
      ((ev1 Event) (ev2 Event))
      (= (and (T ev1) (TLBI-VA ev2) (= (translate_va ev1) (tlbi_va (val_of_cache_op ev2))))
         (tlbi-same-va-page ev1 ev2))))

(declare-fun tlbi-same-ipa-page (Event Event) Bool)
(assert
   (forall ((ev1 Event) (ev2 Event))
      (= (and (T ev1) (TLBI-IPA ev2) (= (translate_ipa ev1) (tlbi_ipa (val_of_cache_op ev2))))
         (tlbi-same-ipa-page ev1 ev2))))

(declare-fun same-va-page (Event Event) Bool)
(assert
   (forall ((ev1 Event) (ev2 Event))
         (= (or (translate-same-va-page ev1 ev2)
                (tlbi-same-va-page ev1 ev2)
                (tlbi-same-va-page ev2 ev1))
            (same-va-page ev1 ev2))))

(declare-fun same-ipa-page (Event Event) Bool)
(assert
   (forall ((ev1 Event) (ev2 Event))
      (= (or (translate-same-ipa-page ev1 ev2)
             (tlbi-same-ipa-page ev1 ev2)
             (tlbi-same-ipa-page ev2 ev1))
         (same-ipa-page ev1 ev2))))

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

; all write/cache-op <-> cache-op pairs are wco-related in one way or another
(assert (forall ((ev1 Event) (ev2 Event))
  (=> (and (or (W ev1) (C ev1))
           (C ev2)
           (not (= ev1 ev2)))
      (or (wco ev1 ev2)
          (wco ev2 ev1)))
))
