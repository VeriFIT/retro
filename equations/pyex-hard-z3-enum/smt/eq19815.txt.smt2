(set-logic QF_S)
(declare-fun V22 () String )
(declare-fun V17 () String )
(declare-fun V39 () String )
(declare-fun V16 () String )
(declare-fun V23 () String )
(declare-fun V7 () String )
(declare-fun V9 () String )
(declare-fun V37 () String )
(declare-fun V8 () String )
(declare-fun V42 () String )
(declare-fun V30 () String )
(declare-fun V35 () String )
(declare-fun V14 () String )
(declare-fun V32 () String )
(declare-fun V0 () String )
(declare-fun V46 () String )
(declare-fun V29 () String )
(declare-fun V24 () String )
(declare-fun V2 () String )
(declare-fun V43 () String )
(declare-fun V31 () String )
(declare-fun V27 () String )
(declare-fun V1 () String )
(declare-fun V15 () String )
(declare-fun V25 () String )
(declare-fun V38 () String )
(declare-fun V28 () String )
(declare-fun V11 () String )
(declare-fun V26 () String )
(declare-fun V49 () String )
(declare-fun V5 () String )
(declare-fun V3 () String )
(declare-fun V45 () String )
(declare-fun V33 () String )
(declare-fun V6 () String )
(declare-fun V10 () String )
(declare-fun V40 () String )
(declare-fun V44 () String )
(declare-fun V12 () String )
(declare-fun V18 () String )
(declare-fun V21 () String )
(declare-fun V19 () String )
(declare-fun V13 () String )
(declare-fun V34 () String )
(declare-fun V4 () String )
(declare-fun V20 () String )
(declare-fun V41 () String )
(declare-fun V36 () String )
(declare-fun V50 () String )
(assert (= "" "A" ) )
(assert (= "" "U" ) )
(assert (= "A" V1 ) )
(assert (= "I" V6 ) )
(assert (= "O" V0 ) )
(assert (= "U" V7 ) )
(assert (= V27 (str.++ (str.++ V42 "I" ) V43 ) ) )
(assert (= V46 (str.++ (str.++ V44 "u" ) V45 ) ) )
(assert (= V34 (str.++ (str.++ V44 "U" ) V45 ) ) )
(assert (= V36 (str.++ (str.++ V42 "i" ) V43 ) ) )
(assert (= V17 (str.++ (str.++ V15 "O" ) V16 ) ) )
(assert (= V29 (str.++ "a" V3 ) ) )
(assert (= V29 (str.++ (str.++ V49 "a" ) V50 ) ) )
(assert (= V3 (str.++ (str.++ V49 "A" ) V50 ) ) )
(assert (= V9 (str.++ (str.++ V18 "O" ) V19 ) ) )
(assert (= V9 (str.++ (str.++ V24 V17 ) V25 ) ) )
(assert (= V5 (str.++ (str.++ V22 "A" ) V23 ) ) )
(assert (= V5 (str.++ (str.++ V12 V13 ) V14 ) ) )
(assert (= V5 (str.++ (str.++ V2 V3 ) V4 ) ) )
(assert (= V11 (str.++ (str.++ V20 "O" ) V21 ) ) )
(assert (= V11 (str.++ (str.++ V8 V9 ) V10 ) ) )
(assert (= (str.++ V36 V31 ) (str.++ (str.++ V33 V34 ) V35 ) ) )
(assert (= (str.++ V36 V31 ) (str.++ (str.++ V37 V38 ) V39 ) ) )
(assert (= (str.++ V29 V13 ) (str.++ (str.++ V40 "I" ) V41 ) ) )
(assert (= (str.++ V29 V13 ) (str.++ (str.++ V30 V31 ) V32 ) ) )
(assert (= (str.++ V29 V13 ) (str.++ (str.++ V26 V27 ) V28 ) ) )
( check-sat )
