(set-logic QF_S)
(declare-fun V43 () String )
(declare-fun V28 () String )
(declare-fun V38 () String )
(declare-fun V51 () String )
(declare-fun V20 () String )
(declare-fun V2 () String )
(declare-fun V18 () String )
(declare-fun V31 () String )
(declare-fun V46 () String )
(declare-fun V7 () String )
(declare-fun V40 () String )
(declare-fun V54 () String )
(declare-fun V56 () String )
(declare-fun V22 () String )
(declare-fun V6 () String )
(declare-fun V27 () String )
(declare-fun V55 () String )
(declare-fun V24 () String )
(declare-fun V34 () String )
(declare-fun V12 () String )
(declare-fun V29 () String )
(declare-fun V23 () String )
(declare-fun V33 () String )
(declare-fun V0 () String )
(declare-fun V57 () String )
(declare-fun V26 () String )
(declare-fun V4 () String )
(declare-fun V14 () String )
(declare-fun V52 () String )
(declare-fun V47 () String )
(declare-fun V15 () String )
(declare-fun V35 () String )
(declare-fun V8 () String )
(declare-fun V17 () String )
(declare-fun V25 () String )
(declare-fun V16 () String )
(declare-fun V30 () String )
(declare-fun V53 () String )
(declare-fun V37 () String )
(declare-fun V19 () String )
(declare-fun V48 () String )
(declare-fun V3 () String )
(declare-fun V42 () String )
(declare-fun V39 () String )
(declare-fun V9 () String )
(declare-fun V5 () String )
(declare-fun V10 () String )
(declare-fun V32 () String )
(declare-fun V1 () String )
(declare-fun V44 () String )
(declare-fun V21 () String )
(declare-fun V49 () String )
(declare-fun V45 () String )
(declare-fun V11 () String )
(declare-fun V50 () String )
(declare-fun V41 () String )
(declare-fun V13 () String )
(declare-fun V36 () String )
(assert (= "" "C" ) )
(assert (= "" "S" ) )
(assert (= "" V43 ) )
(assert (= "" (str.++ (str.++ V21 V22 ) V23 ) ) )
(assert (= "=" V0 ) )
(assert (= "C" V5 ) )
(assert (= "G" V6 ) )
(assert (= "S" V11 ) )
(assert (= V13 (str.++ (str.++ V34 "C" ) V35 ) ) )
(assert (= V13 (str.++ (str.++ V48 V33 ) V49 ) ) )
(assert (= V33 (str.++ (str.++ V31 "C" ) V32 ) ) )
(assert (= V23 V52 ) )
(assert (= V51 (str.++ (str.++ V55 "S" ) V56 ) ) )
(assert (= V57 (str.++ (str.++ V55 "s" ) V56 ) ) )
(assert (= V24 (str.++ (str.++ V53 "g" ) V54 ) ) )
(assert (= V2 (str.++ (str.++ V45 V46 ) V47 ) ) )
(assert (= V2 (str.++ (str.++ V12 V13 ) V14 ) ) )
(assert (= V2 (str.++ (str.++ V25 V26 ) V27 ) ) )
(assert (= V2 (str.++ (str.++ V36 "C" ) V37 ) ) )
(assert (= V8 (str.++ (str.++ V53 "G" ) V54 ) ) )
(assert (= V4 (str.++ (str.++ V38 "=" ) V39 ) ) )
(assert (= V4 (str.++ (str.++ V15 V16 ) V17 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V10 (str.++ (str.++ V42 V43 ) V44 ) ) )
(assert (= V10 (str.++ (str.++ V28 V29 ) V30 ) ) )
(assert (= V10 (str.++ (str.++ V40 "G" ) V41 ) ) )
(assert (= V10 (str.++ (str.++ V18 V19 ) V20 ) ) )
(assert (= V10 (str.++ (str.++ V7 V8 ) V9 ) ) )
(assert (= (str.++ V24 V19 ) (str.++ (str.++ V21 V22 ) V23 ) ) )
(assert (= (str.++ V24 V19 ) (str.++ (str.++ V50 V51 ) V52 ) ) )
( check-sat )
