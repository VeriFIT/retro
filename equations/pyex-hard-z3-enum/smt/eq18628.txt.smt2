(set-logic QF_S)
(declare-fun V15 () String )
(declare-fun V1 () String )
(declare-fun V51 () String )
(declare-fun V2 () String )
(declare-fun V16 () String )
(declare-fun V12 () String )
(declare-fun V24 () String )
(declare-fun V39 () String )
(declare-fun V19 () String )
(declare-fun V40 () String )
(declare-fun V4 () String )
(declare-fun V14 () String )
(declare-fun V35 () String )
(declare-fun V22 () String )
(declare-fun V11 () String )
(declare-fun V31 () String )
(declare-fun V33 () String )
(declare-fun V48 () String )
(declare-fun V49 () String )
(declare-fun V36 () String )
(declare-fun V29 () String )
(declare-fun V41 () String )
(declare-fun V5 () String )
(declare-fun V25 () String )
(declare-fun V3 () String )
(declare-fun V0 () String )
(declare-fun V38 () String )
(declare-fun V42 () String )
(declare-fun V34 () String )
(declare-fun V32 () String )
(declare-fun V7 () String )
(declare-fun V6 () String )
(declare-fun V26 () String )
(declare-fun V20 () String )
(declare-fun V23 () String )
(declare-fun V37 () String )
(declare-fun V13 () String )
(declare-fun V52 () String )
(declare-fun V10 () String )
(declare-fun V18 () String )
(declare-fun V28 () String )
(declare-fun V27 () String )
(declare-fun V43 () String )
(declare-fun V21 () String )
(declare-fun V50 () String )
(declare-fun V17 () String )
(declare-fun V8 () String )
(declare-fun V47 () String )
(declare-fun V46 () String )
(declare-fun V9 () String )
(declare-fun V30 () String )
(assert (= "" "X" ) )
(assert (= "=" V0 ) )
(assert (= "D" V1 ) )
(assert (= "X" V6 ) )
(assert (= V39 (str.++ (str.++ V51 "d" ) V52 ) ) )
(assert (= V3 (str.++ (str.++ V51 "D" ) V52 ) ) )
(assert (= V37 (str.++ (str.++ V48 "X" ) V49 ) ) )
(assert (= V50 (str.++ "x" V37 ) ) )
(assert (= V50 (str.++ (str.++ V48 "x" ) V49 ) ) )
(assert (= V5 (str.++ (str.++ V33 V34 ) V35 ) ) )
(assert (= V5 (str.++ (str.++ V13 V14 ) V15 ) ) )
(assert (= V5 (str.++ (str.++ V23 "D" ) V24 ) ) )
(assert (= V5 (str.++ (str.++ V46 V40 ) V47 ) ) )
(assert (= V5 (str.++ (str.++ V2 V3 ) V4 ) ) )
(assert (= V8 (str.++ (str.++ V30 V31 ) V32 ) ) )
(assert (= V8 (str.++ (str.++ V16 V17 ) V18 ) ) )
(assert (= V10 (str.++ (str.++ V25 "=" ) V26 ) ) )
(assert (= V10 (str.++ (str.++ V11 V5 ) V12 ) ) )
(assert (= V10 (str.++ (str.++ V7 V8 ) V9 ) ) )
(assert (= V22 (str.++ (str.++ V27 V28 ) V29 ) ) )
(assert (= V22 (str.++ (str.++ V19 V20 ) V21 ) ) )
(assert (= (str.++ V39 V40 ) (str.++ (str.++ V41 V42 ) V43 ) ) )
(assert (= (str.++ V39 V40 ) (str.++ (str.++ V36 V37 ) V38 ) ) )
( check-sat )
