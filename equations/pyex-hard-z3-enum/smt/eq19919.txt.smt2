(set-logic QF_S)
(declare-fun V1 () String )
(declare-fun V12 () String )
(declare-fun V4 () String )
(declare-fun V14 () String )
(declare-fun V11 () String )
(declare-fun V38 () String )
(declare-fun V9 () String )
(declare-fun V39 () String )
(declare-fun V32 () String )
(declare-fun V42 () String )
(declare-fun V3 () String )
(declare-fun V17 () String )
(declare-fun V41 () String )
(declare-fun V5 () String )
(declare-fun V18 () String )
(declare-fun V26 () String )
(declare-fun V31 () String )
(declare-fun V43 () String )
(declare-fun V30 () String )
(declare-fun V28 () String )
(declare-fun V10 () String )
(declare-fun V0 () String )
(declare-fun V37 () String )
(declare-fun V16 () String )
(declare-fun V33 () String )
(declare-fun V2 () String )
(declare-fun V27 () String )
(declare-fun V19 () String )
(declare-fun V20 () String )
(declare-fun V6 () String )
(declare-fun V7 () String )
(declare-fun V21 () String )
(declare-fun V25 () String )
(declare-fun V15 () String )
(declare-fun V36 () String )
(declare-fun V22 () String )
(declare-fun V34 () String )
(declare-fun V24 () String )
(declare-fun V23 () String )
(declare-fun V40 () String )
(declare-fun V29 () String )
(declare-fun V13 () String )
(declare-fun V35 () String )
(declare-fun V8 () String )
(assert (= "" "U" ) )
(assert (= "A" V1 ) )
(assert (= "I" V6 ) )
(assert (= "O" V0 ) )
(assert (= "U" V7 ) )
(assert (= V20 (str.++ (str.++ V33 "I" ) V34 ) ) )
(assert (= V37 (str.++ (str.++ V35 "u" ) V36 ) ) )
(assert (= V27 (str.++ (str.++ V35 "U" ) V36 ) ) )
(assert (= V29 (str.++ (str.++ V33 "i" ) V34 ) ) )
(assert (= V22 (str.++ (str.++ V38 "a" ) V39 ) ) )
(assert (= V3 (str.++ (str.++ V38 "A" ) V39 ) ) )
(assert (= V5 (str.++ (str.++ V17 "A" ) V18 ) ) )
(assert (= V5 (str.++ (str.++ V12 V13 ) V14 ) ) )
(assert (= V5 (str.++ (str.++ V2 V3 ) V4 ) ) )
(assert (= V11 (str.++ (str.++ V15 "O" ) V16 ) ) )
(assert (= V11 (str.++ (str.++ V8 V9 ) V10 ) ) )
(assert (= (str.++ V29 V24 ) (str.++ (str.++ V42 "U" ) V43 ) ) )
(assert (= (str.++ V29 V24 ) (str.++ (str.++ V26 V27 ) V28 ) ) )
(assert (= (str.++ V29 V24 ) (str.++ (str.++ V30 V31 ) V32 ) ) )
(assert (= (str.++ V22 V13 ) (str.++ (str.++ V40 "I" ) V41 ) ) )
(assert (= (str.++ V22 V13 ) (str.++ (str.++ V23 V24 ) V25 ) ) )
(assert (= (str.++ V22 V13 ) (str.++ (str.++ V19 V20 ) V21 ) ) )
( check-sat )
