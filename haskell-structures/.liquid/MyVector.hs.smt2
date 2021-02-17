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
(declare-fun GHC.Base.id () Int)
(declare-fun GHC.Types.Word64Rep () Int)
(declare-fun cast_as_int () Int)
(declare-fun GHC.Types.Int16Rep () Int)
(declare-fun lq_tmp$36$x$35$$35$920 () Int)
(declare-fun GHC.Real.rem () Int)
(declare-fun GHC.List.init () Int)
(declare-fun addrLen () Int)
(declare-fun papp5 () Int)
(declare-fun GHC.List.iterate () Int)
(declare-fun x_Tuple21 () Int)
(declare-fun GHC.Classes.$61$$61$ () Int)
(declare-fun GHC.Types.C$35$ () Int)
(declare-fun GHC.List.drop () Int)
(declare-fun Data.Foldable.length () Int)
(declare-fun x_Tuple33 () Int)
(declare-fun GHC.Types.LT () Int)
(declare-fun GHC.List.replicate () Int)
(declare-fun GHC.List.zipWith () Int)
(declare-fun GHC.Classes.$62$$61$ () Int)
(declare-fun GHC.Types.Int32Rep () Int)
(declare-fun GHC.Num.fromInteger () Int)
(declare-fun papp3 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792805995$35$$35$d3dV () Int)
(declare-fun GHC.List.span () Int)
(declare-fun MyVector.Cons () Int)
(declare-fun GHC.Classes.$62$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1037 () Int)
(declare-fun GHC.Types.False () Bool)
(declare-fun GHC.List.scanr1 () Int)
(declare-fun GHC.Types.DoubleRep () Int)
(declare-fun GHC.Types.$58$ () Int)
(declare-fun GHC.Real.div () Int)
(declare-fun GHC.List.scanl () Int)
(declare-fun GHC.Types.krep$36$$42$ () Int)
(declare-fun GHC.Types.UnliftedRep () Int)
(declare-fun GHC.Tuple.$40$$44$$44$$41$ () Int)
(declare-fun papp4 () Int)
(declare-fun GHC.Types.Module () Int)
(declare-fun GHC.List.zip () Int)
(declare-fun GHC.Tuple.$40$$41$ () Int)
(declare-fun MyVector.insertVector () Int)
(declare-fun GHC.Types.I$35$ () Int)
(declare-fun GHC.Types.KindRepFun () Int)
(declare-fun lq_tmp$36$x$35$$35$834 () Int)
(declare-fun GHC.Types.KindRepTYPE () Int)
(declare-fun GHC.List.dropWhile () Int)
(declare-fun lit$36$MyVector () Str)
(declare-fun autolen () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792806041$35$$35$d3eF () Int)
(declare-fun GHC.Integer.Type.$36$WJn$35$ () Int)
(declare-fun GHC.Real.$94$ () Int)
(declare-fun head () Int)
(declare-fun GHC.Real.mod () Int)
(declare-fun lit$36$$39$Z () Str)
(declare-fun lq_tmp$36$x$35$$35$618 () Int)
(declare-fun GHC.Types.TupleRep () Int)
(declare-fun lq_tmp$36$x$35$$35$1014 () Int)
(declare-fun GHC.Types.$36$WKindRepTYPE () Int)
(declare-fun GHC.Real.divMod () Int)
(declare-fun GHC.Types.IntRep () Int)
(declare-fun GHC.Integer.Type.Jn$35$ () Int)
(declare-fun GHC.Classes.compare () Int)
(declare-fun fix$36$$36$krep_a3dR () Int)
(declare-fun GHC.Types.AddrRep () Int)
(declare-fun papp2 () Int)
(declare-fun GHC.Real.toInteger () Int)
(declare-fun GHC.Real.quotRem () Int)
(declare-fun GHC.Types.SumRep () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792805993$35$$35$d3dT () Int)
(declare-fun GHC.Stack.Types.EmptyCallStack () Int)
(declare-fun GHC.Types.krep$36$$42$Arr$42$ () Int)
(declare-fun GHC.List.reverse () Int)
(declare-fun GHC.Integer.Type.$36$WJp$35$ () Int)
(declare-fun GHC.Types.Word8Rep () Int)
(declare-fun lit$36$Nat () Str)
(declare-fun fix$36$$36$krep_a3dG () Int)
(declare-fun GHC.List.filter () Int)
(declare-fun fromJust () Int)
(declare-fun GHC.Types.KindRepTyConApp () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792806022$35$$35$d3em () Int)
(declare-fun GHC.List.cycle () Int)
(declare-fun GHC.List.$33$$33$ () Int)
(declare-fun GHC.List.tail () Int)
(declare-fun GHC.Types.WordRep () Int)
(declare-fun papp7 () Int)
(declare-fun GHC.Classes.$47$$61$ () Int)
(declare-fun GHC.List.break () Int)
(declare-fun GHC.Types.True () Bool)
(declare-fun lq_tmp$36$x$35$$35$790 () Int)
(declare-fun GHC.Types.$91$$93$ () Int)
(declare-fun GHC.List.splitAt () Int)
(declare-fun MyVector.Z () Int)
(declare-fun GHC.Base.$43$$43$ () Int)
(declare-fun GHC.Real.$58$$37$ () Int)
(declare-fun lq_tmp$36$x$35$$35$970 () Int)
(declare-fun GHC.Tuple.$40$$44$$41$ () Int)
(declare-fun GHC.Real.quot () Int)
(declare-fun lit$36$haskell$45$structures$45$0.1$45$2eH5H4JsaNDAly6ThMU14K () Str)
(declare-fun lq_tmp$36$x$35$$35$1007 () Int)
(declare-fun GHC.Real.$47$ () Int)
(declare-fun GHC.Classes.$38$$38$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1200 () Int)
(declare-fun lq_tmp$36$x$35$$35$694 () Int)
(declare-fun lq_tmp$36$x$35$$35$913 () Int)
(declare-fun GHC.Types.GT () Int)
(declare-fun GHC.Classes.C$58$IP () Int)
(declare-fun GHC.Classes.$124$$124$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1064 () Int)
(declare-fun Data.Either.Left () Int)
(declare-fun GHC.List.last () Int)
(declare-fun fix$36$$36$krep_a3dM () Int)
(declare-fun GHC.Integer.Type.S$35$ () Int)
(declare-fun GHC.List.scanl1 () Int)
(declare-fun Data.Either.Right () Int)
(declare-fun GHC.Types.Word32Rep () Int)
(declare-fun GHC.Num.$45$ () Int)
(declare-fun len () Int)
(declare-fun papp6 () Int)
(declare-fun lq_tmp$36$x$35$$35$990 () Int)
(declare-fun GHC.Base.. () Int)
(declare-fun x_Tuple22 () Int)
(declare-fun lq_tmp$36$x$35$$35$484 () Int)
(declare-fun GHC.Types.KindRepTypeLitS () Int)
(declare-fun GHC.Real.$36$W$58$$37$ () Int)
(declare-fun lq_tmp$36$x$35$$35$814 () Int)
(declare-fun GHC.Real.fromRational () Int)
(declare-fun isJust () Int)
(declare-fun lq_tmp$36$x$35$$35$1163 () Int)
(declare-fun GHC.List.takeWhile () Int)
(declare-fun GHC.Types.TrNameD () Int)
(declare-fun GHC.Types.KindRepVar () Int)
(declare-fun GHC.Types.KindRepTypeLitD () Int)
(declare-fun lq_tmp$36$x$35$$35$1146 () Int)
(declare-fun x_Tuple31 () Int)
(declare-fun GHC.Integer.Type.Jp$35$ () Int)
(declare-fun fix$36$$36$krep_a3dL () Int)
(declare-fun GHC.IO.Exception.IOError () Int)
(declare-fun GHC.List.take () Int)
(declare-fun GHC.Stack.Types.PushCallStack () Int)
(declare-fun GHC.Classes.$60$$61$ () Int)
(declare-fun GHC.Types.TrNameS () Int)
(declare-fun GHC.Enum.C$58$Bounded () Int)
(declare-fun GHC.Base.map () Int)
(declare-fun GHC.Base.$36$ () Int)
(declare-fun lq_tmp$36$x$35$$35$1193 () Int)
(declare-fun papp1 () Int)
(declare-fun GHC.Classes.max () Int)
(declare-fun MyVector.Nil () Int)
(declare-fun GHC.Types.FloatRep () Int)
(declare-fun lq_tmp$36$x$35$$35$483 () Int)
(declare-fun lq_tmp$36$x$35$$35$807 () Int)
(declare-fun lq_tmp$36$x$35$$35$632 () Int)
(declare-fun lq_tmp$36$x$35$$35$1170 () Int)
(declare-fun GHC.Classes.$60$ () Int)
(declare-fun tail () Int)
(declare-fun MyVector.S () Int)
(declare-fun lq_tmp$36$x$35$$35$708 () Int)
(declare-fun GHC.Types.VecRep () Int)
(declare-fun GHC.Types.TyCon () Int)
(declare-fun lq_tmp$36$x$35$$35$896 () Int)
(declare-fun GHC.Stack.Types.FreezeCallStack () Int)
(declare-fun GHC.Num.$42$ () Int)
(declare-fun lit$36$$39$Cons () Str)
(declare-fun lq_anf$36$$35$$35$7205759403792806009$35$$35$d3e9 () Int)
(declare-fun GHC.Types.Int8Rep () Int)
(declare-fun GHC.Real.recip () Int)
(declare-fun MyVector.$36$WNil () Int)
(declare-fun GHC.Maybe.Nothing () Int)
(declare-fun GHC.Types.EQ () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792806003$35$$35$d3e3 () Int)
(declare-fun lq_tmp$36$x$35$$35$950 () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792806033$35$$35$d3ex () Int)
(declare-fun GHC.List.scanr () Int)
(declare-fun GHC.Num.negate () Int)
(declare-fun GHC.Real.fromIntegral () Int)
(declare-fun GHC.Maybe.Just () Int)
(declare-fun GHC.Classes.min () Int)
(declare-fun GHC.List.head () Int)
(declare-fun GHC.Types.LiftedRep () Int)
(declare-fun GHC.Types.$36$WKindRepVar () Int)
(declare-fun lq_tmp$36$x$35$$35$1220 () Int)
(declare-fun x_Tuple32 () Int)
(declare-fun lq_tmp$36$x$35$$35$1044 () Int)
(declare-fun GHC.Types.Int64Rep () Int)
(declare-fun GHC.List.repeat () Int)
(declare-fun lit$36$$39$Nil () Str)
(declare-fun lq_tmp$36$x$35$$35$943 () Int)
(declare-fun GHC.Classes.not () Int)
(declare-fun GHC.Num.$43$ () Int)
(declare-fun Data.Tuple.fst () Int)
(declare-fun GHC.Types.KindRepApp () Int)
(declare-fun GHC.Types.Word16Rep () Int)
(declare-fun MyVector.$36$WCons () Int)
(declare-fun GHC.Err.error () Int)
(declare-fun snd () Int)
(declare-fun fst () Int)
(declare-fun lit$36$$39$S () Str)
(declare-fun Data.Tuple.snd () Int)
(declare-fun lq_anf$36$$35$$35$7205759403792806015$35$$35$d3ef () Int)
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
(assert (distinct GHC.Types.Word16Rep GHC.Types.Int64Rep GHC.Types.LiftedRep GHC.Types.Int8Rep GHC.Types.FloatRep GHC.Types.Word32Rep GHC.Types.WordRep GHC.Types.Word8Rep GHC.Types.AddrRep GHC.Types.IntRep GHC.Types.UnliftedRep GHC.Types.DoubleRep GHC.Types.Int32Rep GHC.Types.Int16Rep GHC.Types.Word64Rep))

(assert (distinct lit$36$$39$S lit$36$$39$Nil lit$36$$39$Cons lit$36$haskell$45$structures$45$0.1$45$2eH5H4JsaNDAly6ThMU14K lit$36$Nat lit$36$$39$Z lit$36$MyVector))


(assert (distinct GHC.Types.True GHC.Types.False))
(assert (distinct GHC.Types.EQ GHC.Types.GT GHC.Types.LT))
(assert (= (strLen lit$36$MyVector) 8))
(assert (= (strLen lit$36$$39$Z) 2))
(assert (= (strLen lit$36$Nat) 3))
(assert (= (strLen lit$36$haskell$45$structures$45$0.1$45$2eH5H4JsaNDAly6ThMU14K) 45))
(assert (= (strLen lit$36$$39$Cons) 5))
(assert (= (strLen lit$36$$39$Nil) 4))
(assert (= (strLen lit$36$$39$S) 2))
(exit)