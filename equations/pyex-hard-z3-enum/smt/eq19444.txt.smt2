(set-logic QF_S)
(declare-fun V38 () String )
(declare-fun V9 () String )
(declare-fun V19 () String )
(declare-fun V10 () String )
(declare-fun V49 () String )
(declare-fun V5 () String )
(declare-fun V12 () String )
(declare-fun V18 () String )
(declare-fun V42 () String )
(declare-fun V24 () String )
(declare-fun V27 () String )
(declare-fun V53 () String )
(declare-fun V29 () String )
(declare-fun V16 () String )
(declare-fun V44 () String )
(declare-fun V26 () String )
(declare-fun V55 () String )
(declare-fun V31 () String )
(declare-fun V1 () String )
(declare-fun V52 () String )
(declare-fun V56 () String )
(declare-fun V46 () String )
(declare-fun V6 () String )
(declare-fun V11 () String )
(declare-fun V20 () String )
(declare-fun V57 () String )
(declare-fun V28 () String )
(declare-fun V3 () String )
(declare-fun V4 () String )
(declare-fun V45 () String )
(declare-fun V54 () String )
(declare-fun V22 () String )
(declare-fun V37 () String )
(declare-fun V25 () String )
(declare-fun V51 () String )
(declare-fun V7 () String )
(declare-fun V14 () String )
(declare-fun V43 () String )
(declare-fun V41 () String )
(declare-fun V58 () String )
(declare-fun V35 () String )
(declare-fun V32 () String )
(declare-fun V0 () String )
(declare-fun V8 () String )
(declare-fun V30 () String )
(declare-fun V39 () String )
(declare-fun V23 () String )
(declare-fun V50 () String )
(declare-fun V36 () String )
(declare-fun V15 () String )
(declare-fun V13 () String )
(declare-fun V17 () String )
(declare-fun V2 () String )
(declare-fun V34 () String )
(declare-fun V40 () String )
(declare-fun V21 () String )
(declare-fun V33 () String )
(declare-fun V59 () String )
(declare-fun V60 () String )
(assert (= "" "A" ) )
(assert (= "" "U" ) )
(assert (= "A" V9 ) )
(assert (= "I" V14 ) )
(assert (= "O" V0 ) )
(assert (= "U" V15 ) )
(assert (= V31 (str.++ (str.++ V51 "I" ) V52 ) ) )
(assert (= V46 (str.++ (str.++ V44 "u" ) V45 ) ) )
(assert (= V38 (str.++ (str.++ V44 "U" ) V45 ) ) )
(assert (= V40 (str.++ (str.++ V51 "i" ) V52 ) ) )
(assert (= V57 (str.++ (str.++ V55 "o" ) V56 ) ) )
(assert (= V6 (str.++ (str.++ V55 "O" ) V56 ) ) )
(assert (= V33 (str.++ "a" V11 ) ) )
(assert (= V33 (str.++ (str.++ V53 "a" ) V54 ) ) )
(assert (= V60 (str.++ (str.++ V58 "o" ) V59 ) ) )
(assert (= V11 (str.++ (str.++ V53 "A" ) V54 ) ) )
(assert (= V8 (str.++ (str.++ V21 "O" ) V22 ) ) )
(assert (= V8 (str.++ (str.++ V27 V28 ) V29 ) ) )
(assert (= V8 (str.++ (str.++ V5 V6 ) V7 ) ) )
(assert (= V2 (str.++ (str.++ V58 "O" ) V59 ) ) )
(assert (= V13 (str.++ (str.++ V25 "A" ) V26 ) ) )
(assert (= V13 (str.++ (str.++ V18 V19 ) V20 ) ) )
(assert (= V13 (str.++ (str.++ V10 V11 ) V12 ) ) )
(assert (= V4 (str.++ (str.++ V23 "O" ) V24 ) ) )
(assert (= V4 (str.++ (str.++ V16 V8 ) V17 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= (str.++ V40 V35 ) (str.++ (str.++ V37 V38 ) V39 ) ) )
(assert (= (str.++ V40 V35 ) (str.++ (str.++ V41 V42 ) V43 ) ) )
(assert (= (str.++ V33 V19 ) (str.++ (str.++ V49 "I" ) V50 ) ) )
(assert (= (str.++ V33 V19 ) (str.++ (str.++ V34 V35 ) V36 ) ) )
(assert (= (str.++ V33 V19 ) (str.++ (str.++ V30 V31 ) V32 ) ) )
( check-sat )
