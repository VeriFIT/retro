(set-logic QF_S)
(declare-fun V2 () String )
(declare-fun V0 () String )
(declare-fun V15 () String )
(declare-fun V12 () String )
(declare-fun V57 () String )
(declare-fun V47 () String )
(declare-fun V46 () String )
(declare-fun V17 () String )
(declare-fun V53 () String )
(declare-fun V24 () String )
(declare-fun V54 () String )
(declare-fun V30 () String )
(declare-fun V33 () String )
(declare-fun V39 () String )
(declare-fun V16 () String )
(declare-fun V10 () String )
(declare-fun V56 () String )
(declare-fun V55 () String )
(declare-fun V26 () String )
(declare-fun V13 () String )
(declare-fun V49 () String )
(declare-fun V45 () String )
(declare-fun V61 () String )
(declare-fun V22 () String )
(declare-fun V41 () String )
(declare-fun V60 () String )
(declare-fun V19 () String )
(declare-fun V14 () String )
(declare-fun V32 () String )
(declare-fun V3 () String )
(declare-fun V48 () String )
(declare-fun V34 () String )
(declare-fun V43 () String )
(declare-fun V4 () String )
(declare-fun V6 () String )
(declare-fun V37 () String )
(declare-fun V18 () String )
(declare-fun V5 () String )
(declare-fun V44 () String )
(declare-fun V50 () String )
(declare-fun V38 () String )
(declare-fun V31 () String )
(declare-fun V20 () String )
(declare-fun V59 () String )
(declare-fun V21 () String )
(declare-fun V25 () String )
(declare-fun V27 () String )
(declare-fun V36 () String )
(declare-fun V40 () String )
(declare-fun V1 () String )
(declare-fun V7 () String )
(declare-fun V35 () String )
(declare-fun V58 () String )
(declare-fun V29 () String )
(declare-fun V23 () String )
(declare-fun V11 () String )
(declare-fun V28 () String )
(declare-fun V9 () String )
(declare-fun V8 () String )
(declare-fun V42 () String )
(assert (= "" "C" ) )
(assert (= "" "F" ) )
(assert (= "" V31 ) )
(assert (= "" V28 ) )
(assert (= "" (str.++ (str.++ V30 V31 ) V32 ) ) )
(assert (= "\x09" V14 ) )
(assert (= "=" V15 ) )
(assert (= "C" V4 ) )
(assert (= "F" V8 ) )
(assert (= "L" V13 ) )
(assert (= V12 (str.++ (str.++ V33 "F" ) V34 ) ) )
(assert (= V12 (str.++ (str.++ V46 V26 ) V47 ) ) )
(assert (= V12 (str.++ (str.++ V9 V10 ) V11 ) ) )
(assert (= V25 (str.++ (str.++ V60 "f" ) V61 ) ) )
(assert (= V10 (str.++ (str.++ V60 "F" ) V61 ) ) )
(assert (= V57 (str.++ (str.++ V55 "l" ) V56 ) ) )
(assert (= V49 (str.++ (str.++ V55 "L" ) V56 ) ) )
(assert (= V24 V41 ) )
(assert (= V24 (str.++ "f" V41 ) ) )
(assert (= V6 (str.++ (str.++ V58 "C" ) V59 ) ) )
(assert (= V43 (str.++ (str.++ V58 "c" ) V59 ) ) )
(assert (= V7 V20 ) )
(assert (= V37 V30 ) )
(assert (= V39 V32 ) )
(assert (= V38 V31 ) )
(assert (= V1 (str.++ (str.++ V18 V19 ) V20 ) ) )
(assert (= V1 (str.++ (str.++ V37 V38 ) V39 ) ) )
(assert (= V1 (str.++ (str.++ V30 V31 ) V32 ) ) )
(assert (= V1 (str.++ (str.++ V35 "C" ) V36 ) ) )
(assert (= V1 (str.++ (str.++ V5 V6 ) V7 ) ) )
(assert (= V3 (str.++ (str.++ V16 V14 ) V17 ) ) )
(assert (= V3 (str.++ (str.++ V27 V28 ) V29 ) ) )
(assert (= V3 (str.++ (str.++ V0 V1 ) V2 ) ) )
(assert (= (str.++ V43 V19 ) (str.++ (str.++ V40 V41 ) V42 ) ) )
(assert (= (str.++ V43 V19 ) (str.++ (str.++ V44 V12 ) V45 ) ) )
(assert (= (str.++ V38 V39 ) (str.++ V31 V32 ) ) )
(assert (= (str.++ (str.++ V53 "L" ) V54 ) (str.++ (str.++ V24 V25 ) V26 ) ) )
(assert (= (str.++ (str.++ V48 V49 ) V50 ) (str.++ (str.++ V24 V25 ) V26 ) ) )
(assert (= (str.++ (str.++ V21 V22 ) V23 ) (str.++ (str.++ V24 V25 ) V26 ) ) )
( check-sat )
