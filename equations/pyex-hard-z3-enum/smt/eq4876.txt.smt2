(set-logic QF_S)
(declare-fun V11 () String )
(declare-fun V27 () String )
(declare-fun V2 () String )
(declare-fun V19 () String )
(declare-fun V6 () String )
(declare-fun V18 () String )
(declare-fun V26 () String )
(declare-fun V17 () String )
(declare-fun V12 () String )
(declare-fun V4 () String )
(declare-fun V21 () String )
(declare-fun V25 () String )
(declare-fun V30 () String )
(declare-fun V15 () String )
(declare-fun V23 () String )
(declare-fun V22 () String )
(declare-fun V5 () String )
(declare-fun V33 () String )
(declare-fun V9 () String )
(declare-fun V24 () String )
(declare-fun V3 () String )
(declare-fun V10 () String )
(declare-fun V8 () String )
(declare-fun V32 () String )
(declare-fun V14 () String )
(declare-fun V1 () String )
(declare-fun V34 () String )
(declare-fun V20 () String )
(declare-fun V28 () String )
(declare-fun V16 () String )
(declare-fun V0 () String )
(declare-fun V13 () String )
(declare-fun V7 () String )
(declare-fun V31 () String )
(declare-fun V29 () String )
(assert (= "" "Z" ) )
(assert (= "" V23 ) )
(assert (= "," V9 ) )
(assert (= "/" V0 ) )
(assert (= ":" V14 ) )
(assert (= "Z" V5 ) )
(assert (= V2 (str.++ (str.++ V33 V34 ) V19 ) ) )
(assert (= V2 (str.++ (str.++ V6 V7 ) V8 ) ) )
(assert (= V2 (str.++ (str.++ V17 V18 ) V19 ) ) )
(assert (= V32 V7 ) )
(assert (= V21 (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= V11 (str.++ (str.++ V25 V26 ) V27 ) ) )
(assert (= V4 (str.++ (str.++ V30 "/" ) V31 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V13 (str.++ (str.++ V28 "," ) V29 ) ) )
(assert (= V13 (str.++ (str.++ V20 V21 ) V16 ) ) )
(assert (= V13 (str.++ (str.++ V10 V11 ) V12 ) ) )
(assert (= V13 (str.++ (str.++ V15 V4 ) V16 ) ) )
( check-sat )
