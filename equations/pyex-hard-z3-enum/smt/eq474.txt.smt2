(set-logic QF_S)
(declare-fun V26 () String )
(declare-fun V36 () String )
(declare-fun V39 () String )
(declare-fun V17 () String )
(declare-fun V40 () String )
(declare-fun V16 () String )
(declare-fun V30 () String )
(declare-fun V29 () String )
(declare-fun V11 () String )
(declare-fun V33 () String )
(declare-fun V1 () String )
(declare-fun V32 () String )
(declare-fun V14 () String )
(declare-fun V10 () String )
(declare-fun V22 () String )
(declare-fun V27 () String )
(declare-fun V4 () String )
(declare-fun V0 () String )
(declare-fun V42 () String )
(declare-fun V37 () String )
(declare-fun V3 () String )
(declare-fun V31 () String )
(declare-fun V21 () String )
(declare-fun V15 () String )
(declare-fun V6 () String )
(declare-fun V13 () String )
(declare-fun V18 () String )
(declare-fun V8 () String )
(declare-fun V23 () String )
(declare-fun V28 () String )
(declare-fun V5 () String )
(declare-fun V41 () String )
(declare-fun V9 () String )
(declare-fun V25 () String )
(declare-fun V12 () String )
(declare-fun V38 () String )
(declare-fun V19 () String )
(declare-fun V2 () String )
(declare-fun V7 () String )
(declare-fun V20 () String )
(declare-fun V24 () String )
(assert (= "" "Q" ) )
(assert (= "" V27 ) )
(assert (= "=" V10 ) )
(assert (= "I" V0 ) )
(assert (= "Q" V9 ) )
(assert (= V38 (str.++ "q" V32 ) ) )
(assert (= V38 (str.++ (str.++ V36 "q" ) V37 ) ) )
(assert (= V32 (str.++ (str.++ V36 "Q" ) V37 ) ) )
(assert (= V17 (str.++ (str.++ V39 "i" ) V40 ) ) )
(assert (= V6 (str.++ (str.++ V39 "I" ) V40 ) ) )
(assert (= V16 (str.++ (str.++ V41 "i" ) V42 ) ) )
(assert (= V8 (str.++ (str.++ V22 "I" ) V23 ) ) )
(assert (= V8 (str.++ (str.++ V29 V18 ) V30 ) ) )
(assert (= V8 (str.++ (str.++ V5 V6 ) V7 ) ) )
(assert (= V2 (str.++ (str.++ V41 "I" ) V42 ) ) )
(assert (= V4 (str.++ (str.++ V26 V27 ) V28 ) ) )
(assert (= V4 (str.++ (str.++ V19 V20 ) V21 ) ) )
(assert (= V4 (str.++ (str.++ V24 "I" ) V25 ) ) )
(assert (= V4 (str.++ (str.++ V11 V8 ) V12 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= (str.++ (str.++ V31 V32 ) V33 ) (str.++ (str.++ V16 V17 ) V18 ) ) )
(assert (= (str.++ (str.++ V13 V14 ) V15 ) (str.++ (str.++ V16 V17 ) V18 ) ) )
( check-sat )
