
(define-fun last_write_to_$LEN ((addr (_ BitVec 64)) (v (_ BitVec 64))) Bool
  (exists ((ev Event))
    (or (and (= (val_of_$LEN ev) ((_ extract $LEN_MINUS_1 0) v))
             (= (addr_of ev) addr)
             (not (exists ((ev2 Event))
                    (co ev ev2))))
        (and (= v $INITIAL)
             (= ev IW)
             (not (exists ((ev2 Event))
                    (and (co IW ev2)
                         (= (addr_of ev2) addr))))))))
