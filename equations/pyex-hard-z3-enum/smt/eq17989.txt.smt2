(set-logic QF_S)
(declare-fun V15 () String )
(declare-fun V14 () String )
(declare-fun V34 () String )
(declare-fun V0 () String )
(declare-fun V24 () String )
(declare-fun V22 () String )
(declare-fun V11 () String )
(declare-fun V17 () String )
(declare-fun V30 () String )
(declare-fun V45 () String )
(declare-fun V26 () String )
(declare-fun V37 () String )
(declare-fun V2 () String )
(declare-fun V1 () String )
(declare-fun V46 () String )
(declare-fun V23 () String )
(declare-fun V31 () String )
(declare-fun V7 () String )
(declare-fun V5 () String )
(declare-fun V13 () String )
(declare-fun V20 () String )
(declare-fun V42 () String )
(declare-fun V16 () String )
(declare-fun V6 () String )
(declare-fun V18 () String )
(declare-fun V29 () String )
(declare-fun V4 () String )
(declare-fun V9 () String )
(declare-fun V27 () String )
(declare-fun V48 () String )
(declare-fun V35 () String )
(declare-fun V53 () String )
(declare-fun V52 () String )
(declare-fun V8 () String )
(declare-fun V28 () String )
(declare-fun V12 () String )
(declare-fun V21 () String )
(declare-fun V44 () String )
(declare-fun V10 () String )
(declare-fun V3 () String )
(declare-fun V38 () String )
(declare-fun V41 () String )
(declare-fun V47 () String )
(declare-fun V19 () String )
(declare-fun V49 () String )
(declare-fun V25 () String )
(declare-fun V33 () String )
(declare-fun V32 () String )
(declare-fun V43 () String )
(declare-fun V36 () String )
(assert (= "" "B" ) )
(assert (= "" V26 ) )
(assert (= "" (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= " " V7 ) )
(assert (= "=" V8 ) )
(assert (= "B" V0 ) )
(assert (= "C" V5 ) )
(assert (= "F" V6 ) )
(assert (= V33 (str.++ (str.++ V41 "F" ) V42 ) ) )
(assert (= V43 (str.++ (str.++ V41 "f" ) V42 ) ) )
(assert (= V35 V26 ) )
(assert (= V35 (str.++ (str.++ V52 "c" ) V53 ) ) )
(assert (= V26 (str.++ (str.++ V52 "C" ) V53 ) ) )
(assert (= V2 (str.++ (str.++ V48 "B" ) V49 ) ) )
(assert (= V28 (str.++ (str.++ V48 "b" ) V49 ) ) )
(assert (= V3 V14 ) )
(assert (= V22 V17 ) )
(assert (= V24 V19 ) )
(assert (= V23 V18 ) )
(assert (= V4 (str.++ (str.++ V12 V13 ) V14 ) ) )
(assert (= V4 (str.++ (str.++ V22 V23 ) V24 ) ) )
(assert (= V4 (str.++ (str.++ V17 V18 ) V19 ) ) )
(assert (= V4 (str.++ (str.++ V20 "B" ) V21 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V11 (str.++ (str.++ V15 V7 ) V16 ) ) )
(assert (= V11 (str.++ (str.++ V9 V4 ) V10 ) ) )
(assert (= (str.++ V35 V30 ) (str.++ (str.++ V44 "F" ) V45 ) ) )
(assert (= (str.++ V35 V30 ) (str.++ (str.++ V36 V37 ) V38 ) ) )
(assert (= (str.++ V35 V30 ) (str.++ (str.++ V32 V33 ) V34 ) ) )
(assert (= (str.++ V28 V13 ) (str.++ (str.++ V46 "C" ) V47 ) ) )
(assert (= (str.++ V28 V13 ) (str.++ (str.++ V25 V26 ) V27 ) ) )
(assert (= (str.++ V28 V13 ) (str.++ (str.++ V29 V30 ) V31 ) ) )
(assert (= (str.++ V23 V24 ) (str.++ V18 V19 ) ) )
( check-sat )
