(set-logic QF_S)
(declare-fun V7 () String )
(declare-fun V5 () String )
(declare-fun V3 () String )
(declare-fun V0 () String )
(declare-fun V27 () String )
(declare-fun V28 () String )
(declare-fun V29 () String )
(declare-fun V11 () String )
(declare-fun V14 () String )
(declare-fun V9 () String )
(declare-fun V19 () String )
(declare-fun V22 () String )
(declare-fun V21 () String )
(declare-fun V24 () String )
(declare-fun V15 () String )
(declare-fun V25 () String )
(declare-fun V18 () String )
(declare-fun V13 () String )
(declare-fun V16 () String )
(declare-fun V10 () String )
(declare-fun V30 () String )
(declare-fun V8 () String )
(declare-fun V6 () String )
(declare-fun V17 () String )
(declare-fun V12 () String )
(declare-fun V26 () String )
(declare-fun V32 () String )
(declare-fun V23 () String )
(declare-fun V20 () String )
(declare-fun V4 () String )
(declare-fun V2 () String )
(declare-fun V31 () String )
(declare-fun V1 () String )
(assert (= "" "A" ) )
(assert (= "" "I" ) )
(assert (= "A" V0 ) )
(assert (= "I" V5 ) )
(assert (= "U" V6 ) )
(assert (= V13 (str.++ (str.++ V29 "I" ) V30 ) ) )
(assert (= V28 V20 ) )
(assert (= V28 (str.++ "u" V20 ) ) )
(assert (= V22 (str.++ (str.++ V29 "i" ) V30 ) ) )
(assert (= V3 V9 ) )
(assert (= V15 (str.++ (str.++ V31 "a" ) V32 ) ) )
(assert (= V2 (str.++ (str.++ V31 "A" ) V32 ) ) )
(assert (= V4 (str.++ (str.++ V10 "A" ) V11 ) ) )
(assert (= V4 (str.++ (str.++ V7 V8 ) V9 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= (str.++ V22 V17 ) (str.++ (str.++ V26 "U" ) V27 ) ) )
(assert (= (str.++ V22 V17 ) (str.++ (str.++ V19 V20 ) V21 ) ) )
(assert (= (str.++ V22 V17 ) (str.++ (str.++ V23 V24 ) V25 ) ) )
(assert (= (str.++ V15 V8 ) (str.++ (str.++ V16 V17 ) V18 ) ) )
(assert (= (str.++ V15 V8 ) (str.++ (str.++ V12 V13 ) V14 ) ) )
( check-sat )
