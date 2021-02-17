(set-option :auto-config false)
(set-option :model true)
(set-option :model.partial false)

(set-option :smt.mbqi false)

(define-sort Str () Int)
(declare-fun strLen (Str) Int)
(declare-fun subString (Str Int Int) Str)
(declare-fun concatString (Str Str) Str)
(define-sort Elt () Int)
(define-sort LSet () (Array Elt Bool))
(define-fun smt_set_emp () LSet ((as const LSet) false))
(define-fun smt_set_mem ((x Elt) (s LSet)) Bool (select s x))
(define-fun smt_set_add ((s LSet) (x Elt)) LSet (store s x true))
(define-fun smt_set_cup ((s1 LSet) (s2 LSet)) LSet ((_ map or) s1 s2))
(define-fun smt_set_cap ((s1 LSet) (s2 LSet)) LSet ((_ map and) s1 s2))
(define-fun smt_set_com ((s LSet)) LSet ((_ map not) s))
(define-fun smt_set_dif ((s1 LSet) (s2 LSet)) LSet (smt_set_cap s1 (smt_set_com s2)))
(define-fun smt_set_sub ((s1 LSet) (s2 LSet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-sort Map () (Array Elt Elt))
(define-fun smt_map_sel ((m Map) (k Elt)) Elt (select m k))
(define-fun smt_map_sto ((m Map) (k Elt) (v Elt)) Map (store m k v))
(define-fun smt_map_cup ((m1 Map) (m2 Map)) Map ((_ map (+ (Elt Elt) Elt)) m1 m2))
(define-fun smt_map_def ((v Elt)) Map ((as const (Map)) v))
(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))
(define-fun Z3_OP_MUL ((x Int) (y Int)) Int (* x y))
(define-fun Z3_OP_DIV ((x Int) (y Int)) Int (div x y))
(declare-fun fix$36$$36$dIP_a1t6 () Int)
(declare-fun GHC.Base.id () Int)
(declare-fun cast_as_int () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803016$35$$35$d2rS () Int)
(declare-fun GHC.Real.rem () Int)
(declare-fun GHC.List.init () Int)
(declare-fun addrLen () Int)
(declare-fun ds_d2rx () Int)
(declare-fun lq_tmp$36$x$35$$35$784 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803014$35$$35$d2rQ () Int)
(declare-fun papp5 () Int)
(declare-fun lq_tmp$36$x$35$$35$748 () Int)
(declare-fun GHC.List.iterate () Int)
(declare-fun ds_d2rh () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun xs$35$$35$a1sl () Int)
(declare-fun GHC.Classes.$61$$61$ () Int)
(declare-fun GHC.Types.C$35$ () Int)
(declare-fun GHC.List.drop () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803051$35$$35$d2sr () Int)
(declare-fun VV$35$$35$F$35$$35$18 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4 () Str)
(declare-fun Data.Foldable.length () Int)
(declare-fun x_Tuple33 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5 () Str)
(declare-fun GHC.Types.LT () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803036$35$$35$d2sc () Int)
(declare-fun GHC.List.replicate () Int)
(declare-fun GHC.List.zipWith () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803034$35$$35$d2sa () Int)
(declare-fun lq_tmp$36$x$35$$35$505 () Int)
(declare-fun ds_d2rC () Int)
(declare-fun GHC.Classes.$62$$61$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803013$35$$35$d2rP () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803048$35$$35$d2so () Str)
(declare-fun GHC.Num.fromInteger () Int)
(declare-fun papp3 () Int)
(declare-fun x$35$$35$a1si () Int)
(declare-fun GHC.List.span () Int)
(declare-fun xs$35$$35$a1sj () Int)
(declare-fun GHC.Classes.$62$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803040$35$$35$d2sg () Int)
(declare-fun GHC.Types.False () Bool)
(declare-fun GHC.List.scanr1 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803039$35$$35$d2sf () Int)
(declare-fun GHC.Types.$58$ () Int)
(declare-fun GHC.Real.div () Int)
(declare-fun GHC.List.scanl () Int)
(declare-fun lit$36$error () Str)
(declare-fun GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Types.Module () Int)
(declare-fun lq_tmp$36$x$35$$35$749 () Int)
(declare-fun ds_d2ri () Int)
(declare-fun VV$35$$35$F$35$$35$12 () Str)
(declare-fun GHC.List.zip () Int)
(declare-fun GHC.Tuple.$40$$41$ () Int)
(declare-fun GHC.Types.I$35$ () Int)
(declare-fun GHC.Stack.Types.SrcLoc () Int)
(declare-fun GHC.Num.$36$fNumInt () Int)
(declare-fun GHC.CString.unpackCString$35$ () Int)
(declare-fun lq_karg$36$VV$35$$35$629$35$$35$k_$35$$35$630 () Int)
(declare-fun GHC.List.dropWhile () Int)
(declare-fun autolen () Int)
(declare-fun VV$35$$35$F$35$$35$6 () Int)
(declare-fun GHC.Integer.Type.$36$WJn$35$ () Int)
(declare-fun GHC.Real.$94$ () Int)
(declare-fun lq_tmp$36$x$35$$35$623 () Int)
(declare-fun head () Int)
(declare-fun GHC.Real.mod () Int)
(declare-fun GHC.Real.divMod () Int)
(declare-fun GHC.Integer.Type.Jn$35$ () Int)
(declare-fun lq_karg$36$lq_tmp$36$x$35$$35$620$35$$35$k_$35$$35$630 () Int)
(declare-fun GHC.Classes.compare () Int)
(declare-fun papp2 () Int)
(declare-fun GHC.Real.toInteger () Int)
(declare-fun GHC.Real.quotRem () Int)
(declare-fun GHC.Stack.Types.EmptyCallStack () Int)
(declare-fun lq_tmp$36$x$35$$35$616 () Int)
(declare-fun GHC.Stack.Types.emptyCallStack () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803015$35$$35$d2rR () Int)
(declare-fun GHC.List.reverse () Int)
(declare-fun GHC.Integer.Type.$36$WJp$35$ () Int)
(declare-fun GHC.List.filter () Int)
(declare-fun Lists.$33$$33$$33$ () Int)
(declare-fun fromJust () Int)
(declare-fun lq_karg$36$VV$35$$35$621$35$$35$k_$35$$35$622 () Int)
(declare-fun GHC.List.cycle () Int)
(declare-fun GHC.List.$33$$33$ () Int)
(declare-fun GHC.List.tail () Int)
(declare-fun papp7 () Int)
(declare-fun GHC.Classes.$47$$61$ () Int)
(declare-fun lit$36$Lists.hs () Str)
(declare-fun lq_anf$36$$35$$35$7205759403792803037$35$$35$d2sd () Int)
(declare-fun GHC.List.break () Int)
(declare-fun GHC.Types.True () Bool)
(declare-fun lq_tmp$36$x$35$$35$790 () Int)
(declare-fun GHC.Types.$91$$93$ () Int)
(declare-fun GHC.List.splitAt () Int)
(declare-fun GHC.Base.$43$$43$ () Int)
(declare-fun GHC.Real.$58$$37$ () Int)
(declare-fun GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun GHC.Real.quot () Int)
(declare-fun GHC.Real.$47$ () Int)
(declare-fun lq_karg$36$VV$35$$35$626$35$$35$k_$35$$35$627 () Int)
(declare-fun fldList () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn () Int)
(declare-fun GHC.Classes.$38$$38$ () Int)
(declare-fun lit$36$Lists () Str)
(declare-fun lq_anf$36$$35$$35$7205759403792803049$35$$35$d2sp () Str)
(declare-fun lq_anf$36$$35$$35$7205759403792803045$35$$35$d2sl () Int)
(declare-fun VV$35$$35$F$35$$35$2 () Int)
(declare-fun lit$36$impossible () Str)
(declare-fun lq_anf$36$$35$$35$7205759403792803041$35$$35$d2sh () Int)
(declare-fun GHC.Types.GT () Int)
(declare-fun GHC.Classes.C$58$IP () Int)
(declare-fun VV$35$$35$F$35$$35$20 () Int)
(declare-fun GHC.Classes.$124$$124$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6 () Str)
(declare-fun lq_tmp$36$x$35$$35$1039 () Int)
(declare-fun Data.Either.Left () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj () Int)
(declare-fun GHC.List.last () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7 () Str)
(declare-fun GHC.Integer.Type.S$35$ () Int)
(declare-fun GHC.List.scanl1 () Int)
(declare-fun Data.Either.Right () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803038$35$$35$d2se () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3 () Str)
(declare-fun GHC.Num.$45$ () Int)
(declare-fun len () Int)
(declare-fun papp6 () Int)
(declare-fun lq_tmp$36$x$35$$35$918 () Int)
(declare-fun VV$35$$35$F$35$$35$9 () Int)
(declare-fun GHC.Base.. () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2 () Str)
(declare-fun GHC.Real.$36$W$58$$37$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803044$35$$35$d2sk () Int)
(declare-fun lq_tmp$36$x$35$$35$1026 () Int)
(declare-fun GHC.Real.fromRational () Int)
(declare-fun isJust () Int)
(declare-fun Lists.size () Int)
(declare-fun VV$35$$35$F$35$$35$4 () Int)
(declare-fun GHC.List.takeWhile () Int)
(declare-fun GHC.Types.TrNameD () Int)
(declare-fun GHC.Stack.Types.pushCallStack () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803052$35$$35$d2ss () Int)
(declare-fun VV$35$$35$F$35$$35$21 () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803058$35$$35$d2sy () Int)
(declare-fun GHC.Integer.Type.Jp$35$ () Int)
(declare-fun GHC.IO.Exception.IOError () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803035$35$$35$d2sb () Int)
(declare-fun GHC.List.take () Int)
(declare-fun GHC.Stack.Types.PushCallStack () Int)
(declare-fun GHC.Classes.$60$$61$ () Int)
(declare-fun GHC.Types.TrNameS () Int)
(declare-fun GHC.Enum.C$58$Bounded () Int)
(declare-fun GHC.Base.map () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803054$35$$35$d2su () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803056$35$$35$d2sw () Int)
(declare-fun GHC.Base.$36$ () Int)
(declare-fun papp1 () Int)
(declare-fun GHC.Classes.max () Int)
(declare-fun x$35$$35$a1sk () Int)
(declare-fun lit$36$popl21$45$liquid$45$haskell$45$tutorial$45$0.1$45$5tzy0dlL1WbGfrd1UeLlAF () Str)
(declare-fun lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9 () Str)
(declare-fun Lists.i42 () Int)
(declare-fun GHC.Classes.$60$ () Int)
(declare-fun tail () Int)
(declare-fun GHC.Stack.Types.FreezeCallStack () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8 () Str)
(declare-fun lq_karg$36$Lists.i42$35$$35$k_$35$$35$630 () Int)
(declare-fun GHC.Num.$42$ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803053$35$$35$d2st () Int)
(declare-fun lq_karg$36$Lists.i42$35$$35$k_$35$$35$622 () Int)
(declare-fun lq_tmp$36$x$35$$35$589 () Int)
(declare-fun GHC.Real.recip () Int)
(declare-fun lq_tmp$36$x$35$$35$747 () Int)
(declare-fun GHC.Maybe.Nothing () Int)
(declare-fun lq_tmp$36$x$35$$35$837 () Int)
(declare-fun GHC.Types.EQ () Int)
(declare-fun GHC.List.scanr () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803046$35$$35$d2sm () Int)
(declare-fun GHC.Num.negate () Int)
(declare-fun GHC.Real.fromIntegral () Int)
(declare-fun GHC.Maybe.Just () Int)
(declare-fun lq_karg$36$Lists.i42$35$$35$k_$35$$35$627 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803042$35$$35$d2si () Int)
(declare-fun GHC.Classes.min () Int)
(declare-fun GHC.List.head () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792803011$35$$35$d2rN () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun GHC.List.repeat () Int)
(declare-fun GHC.Classes.not () Int)
(declare-fun GHC.Num.$43$ () Int)
(declare-fun Data.Tuple.fst () Int)
(declare-fun GHC.Err.error () Int)
(declare-fun snd () Int)
(declare-fun fst () Int)
(declare-fun Data.Tuple.snd () Int)
(declare-fun apply$35$$35$13 (Int (_ BitVec 32)) Bool)
(declare-fun apply$35$$35$9 (Int Str) Bool)
(declare-fun apply$35$$35$6 (Int Bool) Str)
(declare-fun apply$35$$35$11 (Int Str) (_ BitVec 32))
(declare-fun apply$35$$35$15 (Int (_ BitVec 32)) (_ BitVec 32))
(declare-fun apply$35$$35$0 (Int Int) Int)
(declare-fun apply$35$$35$8 (Int Str) Int)
(declare-fun apply$35$$35$1 (Int Int) Bool)
(declare-fun apply$35$$35$7 (Int Bool) (_ BitVec 32))
(declare-fun apply$35$$35$14 (Int (_ BitVec 32)) Str)
(declare-fun apply$35$$35$10 (Int Str) Str)
(declare-fun apply$35$$35$5 (Int Bool) Bool)
(declare-fun apply$35$$35$2 (Int Int) Str)
(declare-fun apply$35$$35$12 (Int (_ BitVec 32)) Int)
(declare-fun apply$35$$35$3 (Int Int) (_ BitVec 32))
(declare-fun apply$35$$35$4 (Int Bool) Int)
(declare-fun coerce$35$$35$13 ((_ BitVec 32)) Bool)
(declare-fun coerce$35$$35$9 (Str) Bool)
(declare-fun coerce$35$$35$6 (Bool) Str)
(declare-fun coerce$35$$35$11 (Str) (_ BitVec 32))
(declare-fun coerce$35$$35$15 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun coerce$35$$35$0 (Int) Int)
(declare-fun coerce$35$$35$8 (Str) Int)
(declare-fun coerce$35$$35$1 (Int) Bool)
(declare-fun coerce$35$$35$7 (Bool) (_ BitVec 32))
(declare-fun coerce$35$$35$14 ((_ BitVec 32)) Str)
(declare-fun coerce$35$$35$10 (Str) Str)
(declare-fun coerce$35$$35$5 (Bool) Bool)
(declare-fun coerce$35$$35$2 (Int) Str)
(declare-fun coerce$35$$35$12 ((_ BitVec 32)) Int)
(declare-fun coerce$35$$35$3 (Int) (_ BitVec 32))
(declare-fun coerce$35$$35$4 (Bool) Int)
(declare-fun smt_lambda$35$$35$13 ((_ BitVec 32) Bool) Int)
(declare-fun smt_lambda$35$$35$9 (Str Bool) Int)
(declare-fun smt_lambda$35$$35$6 (Bool Str) Int)
(declare-fun smt_lambda$35$$35$11 (Str (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$15 ((_ BitVec 32) (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$0 (Int Int) Int)
(declare-fun smt_lambda$35$$35$8 (Str Int) Int)
(declare-fun smt_lambda$35$$35$1 (Int Bool) Int)
(declare-fun smt_lambda$35$$35$7 (Bool (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$14 ((_ BitVec 32) Str) Int)
(declare-fun smt_lambda$35$$35$10 (Str Str) Int)
(declare-fun smt_lambda$35$$35$5 (Bool Bool) Int)
(declare-fun smt_lambda$35$$35$2 (Int Str) Int)
(declare-fun smt_lambda$35$$35$12 ((_ BitVec 32) Int) Int)
(declare-fun smt_lambda$35$$35$3 (Int (_ BitVec 32)) Int)
(declare-fun smt_lambda$35$$35$4 (Bool Int) Int)
(declare-fun lam_arg$35$$35$1$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$2$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$3$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$4$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$5$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$6$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$7$35$$35$0 () Int)
(declare-fun lam_arg$35$$35$1$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$2$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$3$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$4$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$5$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$6$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$7$35$$35$8 () Str)
(declare-fun lam_arg$35$$35$1$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$2$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$3$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$4$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$5$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$6$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$7$35$$35$12 () (_ BitVec 32))
(declare-fun lam_arg$35$$35$1$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$2$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$3$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$4$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$5$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$6$35$$35$4 () Bool)
(declare-fun lam_arg$35$$35$7$35$$35$4 () Bool)


(assert (distinct lit$36$popl21$45$liquid$45$haskell$45$tutorial$45$0.1$45$5tzy0dlL1WbGfrd1UeLlAF lit$36$impossible lit$36$Lists lit$36$Lists.hs lit$36$error))

(assert (distinct GHC.Types.True GHC.Types.False))
(assert (distinct GHC.Types.EQ GHC.Types.GT GHC.Types.LT))
(assert (= (strLen lit$36$error) 5))
(assert (= (strLen lit$36$Lists.hs) 8))
(assert (= (strLen lit$36$Lists) 5))
(assert (= (strLen lit$36$impossible) 10))
(assert (= (strLen lit$36$popl21$45$liquid$45$haskell$45$tutorial$45$0.1$45$5tzy0dlL1WbGfrd1UeLlAF) 57))
(push 1)
(assert (and (= Lists.i42 42) (and (>= (apply$35$$35$0 (as Lists.size Int) VV$35$$35$F$35$$35$2) 0) (>= (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2) 0)) (not GHC.Types.False) GHC.Types.True))
(push 1)
(assert (not (= 0 1)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2) (- Lists.i42 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= Lists.i42 (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (>= (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2) 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
(push 1)
(assert (not (= (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2) (+ Lists.i42 1))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (> (apply$35$$35$0 (as len Int) VV$35$$35$F$35$$35$2) 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
(pop 1)
(push 1)
(assert (and (= Lists.i42 42) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_tmp$36$x$35$$35$616) 0) (>= (apply$35$$35$0 (as len Int) lq_tmp$36$x$35$$35$616) 0)) (not GHC.Types.False) (and (>= VV$35$$35$F$35$$35$6 0) (< VV$35$$35$F$35$$35$6 (apply$35$$35$0 (as Lists.size Int) lq_tmp$36$x$35$$35$616))) GHC.Types.True))
(push 1)
(assert (not (= 0 1)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (<= VV$35$$35$F$35$$35$6 Lists.i42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 1)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (< VV$35$$35$F$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (> VV$35$$35$F$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (>= VV$35$$35$F$35$$35$6 Lists.i42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (>= VV$35$$35$F$35$$35$6 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
(push 1)
(assert (not (not (= VV$35$$35$F$35$$35$6 Lists.i42))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (> VV$35$$35$F$35$$35$6 Lists.i42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (not (= VV$35$$35$F$35$$35$6 0))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (<= VV$35$$35$F$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (< VV$35$$35$F$35$$35$6 Lists.i42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 Lists.i42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 0)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 (+ (apply$35$$35$0 (as len Int) lq_tmp$36$x$35$$35$616) Lists.i42))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 (apply$35$$35$0 (as len Int) lq_tmp$36$x$35$$35$616))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 (apply$35$$35$0 (as Lists.size Int) lq_tmp$36$x$35$$35$616))))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (< VV$35$$35$F$35$$35$6 (apply$35$$35$0 (as Lists.size Int) lq_tmp$36$x$35$$35$616))))
(check-sat)
; SMT Says: Unsat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(push 1)
(assert (not (= VV$35$$35$F$35$$35$6 Lists.i42)))
(check-sat)
; SMT Says: Sat
(pop 1)
(pop 1)
(push 1)
(assert (and (= Lists.i42 42) (>= (apply$35$$35$0 (as len Int) ds_d2rC) 0) (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO ds_d2rC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0)) (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO ds_d2rC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0)) (not GHC.Types.False) (>= (apply$35$$35$0 (as len Int) xs$35$$35$a1sj) 0) (= VV$35$$35$F$35$$35$18 (+ lq_anf$36$$35$$35$7205759403792803015$35$$35$d2rR lq_anf$36$$35$$35$7205759403792803016$35$$35$d2rS)) (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO ds_d2rC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) xs$35$$35$a1sj) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) x$35$$35$a1si) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) (+ 1 (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sj))) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) (+ 1 (apply$35$$35$0 (as len Int) xs$35$$35$a1sj))) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO (apply$35$$35$0 (apply$35$$35$0 (as GHC.Types.$58$ Int) x$35$$35$a1si) xs$35$$35$a1sj)) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) xs$35$$35$a1sj) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) x$35$$35$a1si) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) (+ 1 (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sj))) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) (+ 1 (apply$35$$35$0 (as len Int) xs$35$$35$a1sj))) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0)) (= lq_anf$36$$35$$35$7205759403792803014$35$$35$d2rQ 1) (= lq_anf$36$$35$$35$7205759403792803015$35$$35$d2rR lq_anf$36$$35$$35$7205759403792803014$35$$35$d2rQ) (and (= lq_anf$36$$35$$35$7205759403792803016$35$$35$d2rS (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sj)) (>= lq_anf$36$$35$$35$7205759403792803016$35$$35$d2rS 0)) GHC.Types.True))
(push 1)
(assert (not (>= VV$35$$35$F$35$$35$18 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
(pop 1)
(push 1)
(assert (and (= Lists.i42 42) (>= (apply$35$$35$0 (as len Int) ds_d2rC) 0) (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO ds_d2rC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0)) (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO ds_d2rC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0)) (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO ds_d2rC) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO (as GHC.Types.$91$$93$ Int)) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803012$35$$35$d2rO) 0)) (= lq_anf$36$$35$$35$7205759403792803013$35$$35$d2rP 0) (not GHC.Types.False) (= VV$35$$35$F$35$$35$20 lq_anf$36$$35$$35$7205759403792803013$35$$35$d2rP) GHC.Types.True))
(push 1)
(assert (not (>= VV$35$$35$F$35$$35$20 0)))
(check-sat)
; SMT Says: Unsat
(pop 1)
(pop 1)
(push 1)
(assert (and (= lq_anf$36$$35$$35$7205759403792803011$35$$35$d2rN 42) (not GHC.Types.False) (= VV$35$$35$F$35$$35$21 lq_anf$36$$35$$35$7205759403792803011$35$$35$d2rN) GHC.Types.True))
(push 1)
(assert (not (= VV$35$$35$F$35$$35$21 42)))
(check-sat)
; SMT Says: Unsat
(pop 1)
(pop 1)
(push 1)
(assert (and (and (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (and (< lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq (apply$35$$35$0 (as Lists.size Int) ds_d2rh)) (>= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq 0)) (and (< lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq (apply$35$$35$0 (as Lists.size Int) ds_d2rh)) (>= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq 0)) (and (< lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq (apply$35$$35$0 (as Lists.size Int) ds_d2rh)) (>= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq 0)) (>= (apply$35$$35$0 (as len Int) ds_d2rh) 0) (and (< ds_d2ri (apply$35$$35$0 (as Lists.size Int) ds_d2rh)) (>= ds_d2ri 0)) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (exists ((lq_karg$36$VV$35$$35$621$35$$35$k_$35$$35$622 Int) (lq_tmp$36$x$35$$35$937 Int) (lq_karg$36$Lists.i42$35$$35$k_$35$$35$622 Int)) (and (and (= lq_karg$36$VV$35$$35$621$35$$35$k_$35$$35$622 x$35$$35$a1sk) (= lq_tmp$36$x$35$$35$937 x$35$$35$a1sk) (= lq_karg$36$Lists.i42$35$$35$k_$35$$35$622 Lists.i42)) (exists ((VV$35$$35$F$35$$35$4 Int)) (and (and (= lq_karg$36$VV$35$$35$621$35$$35$k_$35$$35$622 VV$35$$35$F$35$$35$4) (= lq_karg$36$Lists.i42$35$$35$k_$35$$35$622 Lists.i42))))))) (= lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2 lit$36$error) (and (>= (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sl) 0) (>= (apply$35$$35$0 (as len Int) xs$35$$35$a1sl) 0)) (= Lists.i42 42) (and (= lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3 lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) (strLen lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) 0)) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn ds_d2rh) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) xs$35$$35$a1sl) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) x$35$$35$a1sk) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) (+ 1 (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sl))) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) (+ 1 (apply$35$$35$0 (as len Int) xs$35$$35$a1sl))) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn (apply$35$$35$0 (apply$35$$35$0 (as GHC.Types.$58$ Int) x$35$$35$a1sk) xs$35$$35$a1sl)) (= (apply$35$$35$0 (as tail Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) xs$35$$35$a1sl) (= (apply$35$$35$0 (as head Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) x$35$$35$a1sk) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) (+ 1 (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sl))) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) (+ 1 (apply$35$$35$0 (as len Int) xs$35$$35$a1sl))) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) (= lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4 lit$36$popl21$45$liquid$45$haskell$45$tutorial$45$0.1$45$5tzy0dlL1WbGfrd1UeLlAF) (and (= (apply$35$$35$0 (as x_Tuple22 Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803042$35$$35$d2si) (= (apply$35$$35$2 (as x_Tuple21 Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) (= (apply$35$$35$0 (as snd Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803042$35$$35$d2si) (= (apply$35$$35$2 (as fst Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3)) (= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq ds_d2ri) (and (= lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5 lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5) (strLen lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5) 0)) (= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq ds_d2ri) (= lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6 lit$36$Lists) (= lq_anf$36$$35$$35$7205759403792803045$35$$35$d2sl lq_anf$36$$35$$35$7205759403792803044$35$$35$d2sk) (and (= lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7 lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7) (strLen lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7) 0)) (and (= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq ds_d2ri) (= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq ds_d2rx) (= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq ds_d2rx) (= lq_anf$36$$35$$35$7205759403792803050$35$$35$d2sq ds_d2rx)) (= lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8 lit$36$Lists.hs) (= lq_anf$36$$35$$35$7205759403792803051$35$$35$d2sr ds_d2rx) (and (= lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9 lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9) (strLen lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9) 0)) (and (>= (apply$35$$35$0 (as Lists.size Int) ds_d2rh) 0) (>= (apply$35$$35$0 (as len Int) ds_d2rh) 0)) (and (= lq_anf$36$$35$$35$7205759403792803051$35$$35$d2sr ds_d2rx) (not (= lq_anf$36$$35$$35$7205759403792803051$35$$35$d2sr 0))) (= lq_anf$36$$35$$35$7205759403792803034$35$$35$d2sa 20) (= lq_anf$36$$35$$35$7205759403792803052$35$$35$d2ss 1) (= lq_anf$36$$35$$35$7205759403792803035$35$$35$d2sb lq_anf$36$$35$$35$7205759403792803034$35$$35$d2sa) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn ds_d2rh) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) (= lq_anf$36$$35$$35$7205759403792803053$35$$35$d2st lq_anf$36$$35$$35$7205759403792803052$35$$35$d2ss) (not GHC.Types.False) (= lq_anf$36$$35$$35$7205759403792803036$35$$35$d2sc 11) (= lq_anf$36$$35$$35$7205759403792803054$35$$35$d2su (- ds_d2ri lq_anf$36$$35$$35$7205759403792803053$35$$35$d2st)) (= lq_anf$36$$35$$35$7205759403792803037$35$$35$d2sd lq_anf$36$$35$$35$7205759403792803036$35$$35$d2sc) (= lq_anf$36$$35$$35$7205759403792803038$35$$35$d2se 20) (= lq_anf$36$$35$$35$7205759403792803039$35$$35$d2sf lq_anf$36$$35$$35$7205759403792803038$35$$35$d2se) (= lq_anf$36$$35$$35$7205759403792803040$35$$35$d2sg 29) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn ds_d2rh) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) GHC.Types.True (= lq_anf$36$$35$$35$7205759403792803041$35$$35$d2sh lq_anf$36$$35$$35$7205759403792803040$35$$35$d2sg) (and (= VV$35$$35$F$35$$35$9 (- ds_d2ri lq_anf$36$$35$$35$7205759403792803053$35$$35$d2st)) (= VV$35$$35$F$35$$35$9 lq_anf$36$$35$$35$7205759403792803054$35$$35$d2su))))
(push 1)
(assert (not (and (>= VV$35$$35$F$35$$35$9 0) (< VV$35$$35$F$35$$35$9 (apply$35$$35$0 (as Lists.size Int) xs$35$$35$a1sl)))))
(check-sat)
; SMT Says: Unsat
(pop 1)
(pop 1)
(push 1)
(assert (and (and (>= (apply$35$$35$0 (as len Int) ds_d2rh) 0) (and (< ds_d2ri (apply$35$$35$0 (as Lists.size Int) ds_d2rh)) (>= ds_d2ri 0)) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) (= lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2 lit$36$error) (and (= VV$35$$35$F$35$$35$12 lq_anf$36$$35$$35$7205759403792803048$35$$35$d2so) (= (apply$35$$35$8 (as len Int) VV$35$$35$F$35$$35$12) (strLen lq_anf$36$$35$$35$7205759403792803048$35$$35$d2so)) (>= (apply$35$$35$8 (as Lists.size Int) VV$35$$35$F$35$$35$12) 0) (>= (apply$35$$35$8 (as len Int) VV$35$$35$F$35$$35$12) 0) (= VV$35$$35$F$35$$35$12 lq_anf$36$$35$$35$7205759403792803049$35$$35$d2sp) (>= (apply$35$$35$8 (as Lists.size Int) VV$35$$35$F$35$$35$12) 0) (>= (apply$35$$35$8 (as len Int) VV$35$$35$F$35$$35$12) 0)) (= Lists.i42 42) (and (= lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3 lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) (strLen lq_anf$36$$35$$35$7205759403792803026$35$$35$d2s2)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) 0)) (= lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4 lit$36$popl21$45$liquid$45$haskell$45$tutorial$45$0.1$45$5tzy0dlL1WbGfrd1UeLlAF) (and (= (apply$35$$35$0 (as x_Tuple22 Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803042$35$$35$d2si) (= (apply$35$$35$2 (as x_Tuple21 Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3) (= (apply$35$$35$0 (as snd Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803042$35$$35$d2si) (= (apply$35$$35$2 (as fst Int) lq_anf$36$$35$$35$7205759403792803043$35$$35$d2sj) lq_anf$36$$35$$35$7205759403792803027$35$$35$d2s3)) (and (= lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5 lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5) (strLen lq_anf$36$$35$$35$7205759403792803028$35$$35$d2s4)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803029$35$$35$d2s5) 0)) (= lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6 lit$36$Lists) (= lq_anf$36$$35$$35$7205759403792803045$35$$35$d2sl lq_anf$36$$35$$35$7205759403792803044$35$$35$d2sk) (and (= lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7 lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7) (strLen lq_anf$36$$35$$35$7205759403792803030$35$$35$d2s6)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803031$35$$35$d2s7) 0)) (= lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8 lit$36$Lists.hs) (and (= lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9 lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9) (strLen lq_anf$36$$35$$35$7205759403792803032$35$$35$d2s8)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803033$35$$35$d2s9) 0)) (and (>= (apply$35$$35$0 (as Lists.size Int) ds_d2rh) 0) (>= (apply$35$$35$0 (as len Int) ds_d2rh) 0)) (= lq_anf$36$$35$$35$7205759403792803034$35$$35$d2sa 20) (= lq_anf$36$$35$$35$7205759403792803035$35$$35$d2sb lq_anf$36$$35$$35$7205759403792803034$35$$35$d2sa) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn ds_d2rh) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) (not GHC.Types.False) (= lq_anf$36$$35$$35$7205759403792803036$35$$35$d2sc 11) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn ds_d2rh) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) (= lq_anf$36$$35$$35$7205759403792803037$35$$35$d2sd lq_anf$36$$35$$35$7205759403792803036$35$$35$d2sc) (and (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn ds_d2rh) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn (as GHC.Types.$91$$93$ Int)) (= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0) (>= (apply$35$$35$0 (as len Int) lq_anf$36$$35$$35$7205759403792803047$35$$35$d2sn) 0)) (= lq_anf$36$$35$$35$7205759403792803038$35$$35$d2se 20) (= lq_anf$36$$35$$35$7205759403792803048$35$$35$d2so lit$36$impossible) (= lq_anf$36$$35$$35$7205759403792803039$35$$35$d2sf lq_anf$36$$35$$35$7205759403792803038$35$$35$d2se) (and (= lq_anf$36$$35$$35$7205759403792803049$35$$35$d2sp lq_anf$36$$35$$35$7205759403792803048$35$$35$d2so) (= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803049$35$$35$d2sp) (strLen lq_anf$36$$35$$35$7205759403792803048$35$$35$d2so)) (>= (apply$35$$35$8 (as Lists.size Int) lq_anf$36$$35$$35$7205759403792803049$35$$35$d2sp) 0) (>= (apply$35$$35$8 (as len Int) lq_anf$36$$35$$35$7205759403792803049$35$$35$d2sp) 0)) (= lq_anf$36$$35$$35$7205759403792803040$35$$35$d2sg 29) GHC.Types.True (= lq_anf$36$$35$$35$7205759403792803041$35$$35$d2sh lq_anf$36$$35$$35$7205759403792803040$35$$35$d2sg)))
(push 1)
(assert (not false))
(check-sat)
; SMT Says: Unsat
(pop 1)
(pop 1)
(exit)
