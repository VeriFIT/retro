(set-logic QF_S)
(declare-fun V21 () String )
(declare-fun V10 () String )
(declare-fun V4 () String )
(declare-fun V38 () String )
(declare-fun V8 () String )
(declare-fun V18 () String )
(declare-fun V16 () String )
(declare-fun V31 () String )
(declare-fun V37 () String )
(declare-fun V7 () String )
(declare-fun V13 () String )
(declare-fun V22 () String )
(declare-fun V1 () String )
(declare-fun V9 () String )
(declare-fun V3 () String )
(declare-fun V14 () String )
(declare-fun V29 () String )
(declare-fun V25 () String )
(declare-fun V20 () String )
(declare-fun V11 () String )
(declare-fun V15 () String )
(declare-fun V28 () String )
(declare-fun V32 () String )
(declare-fun V12 () String )
(declare-fun V30 () String )
(declare-fun V33 () String )
(declare-fun V6 () String )
(declare-fun V2 () String )
(declare-fun V17 () String )
(declare-fun V23 () String )
(declare-fun V34 () String )
(declare-fun V24 () String )
(declare-fun V5 () String )
(declare-fun V19 () String )
(declare-fun V0 () String )
(assert (= "" "I" ) )
(assert (= "A" V0 ) )
(assert (= "I" V5 ) )
(assert (= "U" V6 ) )
(assert (= V18 (str.++ (str.++ V33 "I" ) V34 ) ) )
(assert (= V30 (str.++ (str.++ V28 "u" ) V29 ) ) )
(assert (= V24 (str.++ (str.++ V28 "U" ) V29 ) ) )
(assert (= V13 (str.++ (str.++ V33 "i" ) V34 ) ) )
(assert (= V20 V2 ) )
(assert (= V20 (str.++ "a" V2 ) ) )
(assert (= V2 (str.++ (str.++ V37 "A" ) V38 ) ) )
(assert (= V4 (str.++ (str.++ V15 "A" ) V16 ) ) )
(assert (= V4 (str.++ (str.++ V7 V8 ) V9 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= (str.++ V13 V14 ) (str.++ (str.++ V31 "U" ) V32 ) ) )
(assert (= (str.++ V13 V14 ) (str.++ (str.++ V23 V24 ) V25 ) ) )
(assert (= (str.++ V13 V14 ) (str.++ (str.++ V10 V11 ) V12 ) ) )
(assert (= (str.++ V20 V8 ) (str.++ (str.++ V21 V14 ) V22 ) ) )
(assert (= (str.++ V20 V8 ) (str.++ (str.++ V17 V18 ) V19 ) ) )
( check-sat )
