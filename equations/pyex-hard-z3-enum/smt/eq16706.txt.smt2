(set-logic QF_S)
(declare-fun V7 () String )
(declare-fun V21 () String )
(declare-fun V11 () String )
(declare-fun V51 () String )
(declare-fun V18 () String )
(declare-fun V1 () String )
(declare-fun V14 () String )
(declare-fun V29 () String )
(declare-fun V26 () String )
(declare-fun V2 () String )
(declare-fun V46 () String )
(declare-fun V16 () String )
(declare-fun V27 () String )
(declare-fun V48 () String )
(declare-fun V9 () String )
(declare-fun V41 () String )
(declare-fun V22 () String )
(declare-fun V23 () String )
(declare-fun V38 () String )
(declare-fun V25 () String )
(declare-fun V37 () String )
(declare-fun V17 () String )
(declare-fun V28 () String )
(declare-fun V4 () String )
(declare-fun V44 () String )
(declare-fun V43 () String )
(declare-fun V35 () String )
(declare-fun V49 () String )
(declare-fun V32 () String )
(declare-fun V15 () String )
(declare-fun V50 () String )
(declare-fun V24 () String )
(declare-fun V33 () String )
(declare-fun V47 () String )
(declare-fun V5 () String )
(declare-fun V42 () String )
(declare-fun V0 () String )
(declare-fun V20 () String )
(declare-fun V3 () String )
(declare-fun V6 () String )
(declare-fun V30 () String )
(declare-fun V8 () String )
(declare-fun V12 () String )
(declare-fun V36 () String )
(declare-fun V34 () String )
(declare-fun V45 () String )
(declare-fun V19 () String )
(declare-fun V10 () String )
(declare-fun V31 () String )
(declare-fun V13 () String )
(assert (= "" "B" ) )
(assert (= "" (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= "\x09" V7 ) )
(assert (= "=" V8 ) )
(assert (= "B" V0 ) )
(assert (= "C" V5 ) )
(assert (= "F" V6 ) )
(assert (= V37 (str.++ (str.++ V41 "F" ) V42 ) ) )
(assert (= V43 (str.++ "f" V37 ) ) )
(assert (= V43 (str.++ (str.++ V41 "f" ) V42 ) ) )
(assert (= V18 (str.++ (str.++ V44 "c" ) V45 ) ) )
(assert (= V31 (str.++ (str.++ V44 "C" ) V45 ) ) )
(assert (= V2 (str.++ (str.++ V46 "B" ) V47 ) ) )
(assert (= V33 (str.++ (str.++ V46 "b" ) V47 ) ) )
(assert (= V3 V14 ) )
(assert (= V27 V22 ) )
(assert (= V29 V24 ) )
(assert (= V28 V23 ) )
(assert (= V4 (str.++ (str.++ V12 V13 ) V14 ) ) )
(assert (= V4 (str.++ (str.++ V27 V28 ) V29 ) ) )
(assert (= V4 (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= V4 (str.++ (str.++ V25 "B" ) V26 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V11 (str.++ (str.++ V20 V7 ) V21 ) ) )
(assert (= V11 (str.++ (str.++ V9 V4 ) V10 ) ) )
(assert (= (str.++ V18 V19 ) (str.++ (str.++ V48 "F" ) V49 ) ) )
(assert (= (str.++ V18 V19 ) (str.++ (str.++ V15 V16 ) V17 ) ) )
(assert (= (str.++ V18 V19 ) (str.++ (str.++ V36 V37 ) V38 ) ) )
(assert (= (str.++ V33 V13 ) (str.++ (str.++ V50 "C" ) V51 ) ) )
(assert (= (str.++ V33 V13 ) (str.++ (str.++ V30 V31 ) V32 ) ) )
(assert (= (str.++ V33 V13 ) (str.++ (str.++ V34 V19 ) V35 ) ) )
(assert (= (str.++ V28 V29 ) (str.++ V23 V24 ) ) )
( check-sat )
