(set-logic QF_S)
(declare-fun V39 () String )
(declare-fun V27 () String )
(declare-fun V20 () String )
(declare-fun V10 () String )
(declare-fun V17 () String )
(declare-fun V22 () String )
(declare-fun V41 () String )
(declare-fun V30 () String )
(declare-fun V18 () String )
(declare-fun V21 () String )
(declare-fun V19 () String )
(declare-fun V6 () String )
(declare-fun V0 () String )
(declare-fun V34 () String )
(declare-fun V5 () String )
(declare-fun V23 () String )
(declare-fun V25 () String )
(declare-fun V13 () String )
(declare-fun V1 () String )
(declare-fun V35 () String )
(declare-fun V31 () String )
(declare-fun V28 () String )
(declare-fun V29 () String )
(declare-fun V14 () String )
(declare-fun V4 () String )
(declare-fun V12 () String )
(declare-fun V15 () String )
(declare-fun V9 () String )
(declare-fun V3 () String )
(declare-fun V36 () String )
(declare-fun V24 () String )
(declare-fun V38 () String )
(declare-fun V16 () String )
(declare-fun V11 () String )
(declare-fun V26 () String )
(declare-fun V7 () String )
(declare-fun V8 () String )
(declare-fun V2 () String )
(declare-fun V37 () String )
(declare-fun V40 () String )
(assert (= "" "A" ) )
(assert (= "" "U" ) )
(assert (= "" (str.++ (str.++ V40 "U" ) V41 ) ) )
(assert (= "" (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= "A" V0 ) )
(assert (= "I" V5 ) )
(assert (= "U" V6 ) )
(assert (= V16 (str.++ (str.++ V36 "I" ) V37 ) ) )
(assert (= V28 V24 ) )
(assert (= V31 (str.++ "u" V23 ) ) )
(assert (= V31 (str.++ (str.++ V29 "u" ) V30 ) ) )
(assert (= V23 (str.++ (str.++ V29 "U" ) V30 ) ) )
(assert (= V25 (str.++ "i" V16 ) ) )
(assert (= V25 (str.++ (str.++ V36 "i" ) V37 ) ) )
(assert (= V3 V9 ) )
(assert (= V18 (str.++ "a" V2 ) ) )
(assert (= V18 (str.++ (str.++ V38 "a" ) V39 ) ) )
(assert (= V2 (str.++ (str.++ V38 "A" ) V39 ) ) )
(assert (= V4 (str.++ (str.++ V13 "A" ) V14 ) ) )
(assert (= V4 (str.++ (str.++ V7 V8 ) V9 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V12 (str.++ (str.++ V10 "M" ) V11 ) ) )
(assert (= (str.++ V25 V20 ) (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= (str.++ V25 V20 ) (str.++ (str.++ V26 V27 ) V28 ) ) )
(assert (= (str.++ V18 V8 ) (str.++ (str.++ V34 "I" ) V35 ) ) )
(assert (= (str.++ V18 V8 ) (str.++ (str.++ V19 V20 ) V21 ) ) )
(assert (= (str.++ V18 V8 ) (str.++ (str.++ V15 V16 ) V17 ) ) )
( check-sat )
