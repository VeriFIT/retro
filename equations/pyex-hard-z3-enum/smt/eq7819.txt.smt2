(set-logic QF_S)
(declare-fun V52 () String )
(declare-fun V37 () String )
(declare-fun V43 () String )
(declare-fun V47 () String )
(declare-fun V23 () String )
(declare-fun V40 () String )
(declare-fun V21 () String )
(declare-fun V39 () String )
(declare-fun V38 () String )
(declare-fun V11 () String )
(declare-fun V29 () String )
(declare-fun V3 () String )
(declare-fun V33 () String )
(declare-fun V48 () String )
(declare-fun V49 () String )
(declare-fun V0 () String )
(declare-fun V2 () String )
(declare-fun V13 () String )
(declare-fun V17 () String )
(declare-fun V35 () String )
(declare-fun V27 () String )
(declare-fun V42 () String )
(declare-fun V15 () String )
(declare-fun V30 () String )
(declare-fun V5 () String )
(declare-fun V26 () String )
(declare-fun V22 () String )
(declare-fun V6 () String )
(declare-fun V16 () String )
(declare-fun V14 () String )
(declare-fun V45 () String )
(declare-fun V12 () String )
(declare-fun V46 () String )
(declare-fun V19 () String )
(declare-fun V34 () String )
(declare-fun V10 () String )
(declare-fun V9 () String )
(declare-fun V8 () String )
(declare-fun V4 () String )
(declare-fun V1 () String )
(declare-fun V25 () String )
(declare-fun V24 () String )
(declare-fun V18 () String )
(declare-fun V36 () String )
(declare-fun V32 () String )
(declare-fun V50 () String )
(declare-fun V7 () String )
(declare-fun V31 () String )
(declare-fun V41 () String )
(declare-fun V44 () String )
(declare-fun V20 () String )
(declare-fun V51 () String )
(declare-fun V28 () String )
(assert (= "" "?" ) )
(assert (= "" V32 ) )
(assert (= "&" V8 ) )
(assert (= "/" V0 ) )
(assert (= ":" V17 ) )
(assert (= ";" V7 ) )
(assert (= "=" V2 ) )
(assert (= "?" V1 ) )
(assert (= V12 (str.++ (str.++ V34 V35 ) V36 ) ) )
(assert (= V12 (str.++ (str.++ V44 "?" ) V45 ) ) )
(assert (= V12 (str.++ (str.++ V26 V6 ) V27 ) ) )
(assert (= V12 (str.++ (str.++ V9 V10 ) V11 ) ) )
(assert (= V6 (str.++ (str.++ V42 "=" ) V43 ) ) )
(assert (= V6 (str.++ (str.++ V28 V29 ) V30 ) ) )
(assert (= V6 (str.++ (str.++ V3 V4 ) V5 ) ) )
(assert (= V4 (str.++ (str.++ V40 "E" ) V41 ) ) )
(assert (= V14 (str.++ (str.++ V46 "@" ) V47 ) ) )
(assert (= V14 (str.++ (str.++ V18 V19 ) V20 ) ) )
(assert (= V14 (str.++ (str.++ V31 V32 ) V33 ) ) )
(assert (= V32 (str.++ (str.++ V37 V38 ) V39 ) ) )
(assert (= V16 (str.++ (str.++ V24 V12 ) V25 ) ) )
(assert (= V16 (str.++ (str.++ V48 "/" ) V49 ) ) )
(assert (= V16 (str.++ (str.++ V13 V14 ) V15 ) ) )
(assert (= V23 (str.++ (str.++ V21 V16 ) V22 ) ) )
(assert (= V23 (str.++ (str.++ V51 "://" ) V52 ) ) )
(assert (= V23 (str.++ "mongodb://" V50 ) ) )
( check-sat )
