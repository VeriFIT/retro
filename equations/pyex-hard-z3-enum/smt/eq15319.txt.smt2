(set-logic QF_S)
(declare-fun V16 () String )
(declare-fun V18 () String )
(declare-fun V51 () String )
(declare-fun V35 () String )
(declare-fun V24 () String )
(declare-fun V29 () String )
(declare-fun V14 () String )
(declare-fun V9 () String )
(declare-fun V3 () String )
(declare-fun V15 () String )
(declare-fun V7 () String )
(declare-fun V57 () String )
(declare-fun V26 () String )
(declare-fun V17 () String )
(declare-fun V5 () String )
(declare-fun V11 () String )
(declare-fun V25 () String )
(declare-fun V47 () String )
(declare-fun V36 () String )
(declare-fun V19 () String )
(declare-fun V28 () String )
(declare-fun V32 () String )
(declare-fun V8 () String )
(declare-fun V60 () String )
(declare-fun V58 () String )
(declare-fun V21 () String )
(declare-fun V45 () String )
(declare-fun V52 () String )
(declare-fun V0 () String )
(declare-fun V6 () String )
(declare-fun V20 () String )
(declare-fun V2 () String )
(declare-fun V1 () String )
(declare-fun V59 () String )
(declare-fun V13 () String )
(declare-fun V23 () String )
(declare-fun V61 () String )
(declare-fun V43 () String )
(declare-fun V42 () String )
(declare-fun V34 () String )
(declare-fun V4 () String )
(declare-fun V38 () String )
(declare-fun V44 () String )
(declare-fun V41 () String )
(declare-fun V40 () String )
(declare-fun V31 () String )
(declare-fun V12 () String )
(declare-fun V62 () String )
(declare-fun V49 () String )
(declare-fun V37 () String )
(declare-fun V27 () String )
(declare-fun V33 () String )
(declare-fun V22 () String )
(declare-fun V39 () String )
(declare-fun V10 () String )
(declare-fun V50 () String )
(declare-fun V48 () String )
(declare-fun V30 () String )
(declare-fun V46 () String )
(assert (= "" "A" ) )
(assert (= "" "S" ) )
(assert (= "" V41 ) )
(assert (= "=" V0 ) )
(assert (= "A" V1 ) )
(assert (= "F" V6 ) )
(assert (= "S" V7 ) )
(assert (= V46 (str.++ (str.++ V59 "a" ) V60 ) ) )
(assert (= V3 (str.++ (str.++ V59 "A" ) V60 ) ) )
(assert (= V44 (str.++ (str.++ V57 "F" ) V58 ) ) )
(assert (= V29 (str.++ (str.++ V27 "S" ) V28 ) ) )
(assert (= V52 (str.++ (str.++ V57 "f" ) V58 ) ) )
(assert (= V5 (str.++ (str.++ V40 V41 ) V42 ) ) )
(assert (= V5 (str.++ (str.++ V17 V18 ) V19 ) ) )
(assert (= V5 (str.++ (str.++ V30 "A" ) V31 ) ) )
(assert (= V5 (str.++ (str.++ V14 V15 ) V16 ) ) )
(assert (= V5 (str.++ (str.++ V2 V3 ) V4 ) ) )
(assert (= V9 (str.++ (str.++ V37 V38 ) V39 ) ) )
(assert (= V9 (str.++ (str.++ V20 V21 ) V22 ) ) )
(assert (= V11 (str.++ (str.++ V32 "=" ) V33 ) ) )
(assert (= V11 (str.++ (str.++ V12 V5 ) V13 ) ) )
(assert (= V11 (str.++ (str.++ V8 V9 ) V10 ) ) )
(assert (= V26 (str.++ (str.++ V34 V35 ) V36 ) ) )
(assert (= V26 (str.++ (str.++ V23 V24 ) V25 ) ) )
(assert (= (str.++ V46 V15 ) (str.++ (str.++ V61 "F" ) V62 ) ) )
(assert (= (str.++ V46 V15 ) (str.++ (str.++ V47 V48 ) V49 ) ) )
(assert (= (str.++ V46 V15 ) (str.++ (str.++ V43 V44 ) V45 ) ) )
(assert (= (str.++ V52 V48 ) (str.++ (str.++ V50 V29 ) V51 ) ) )
( check-sat )
