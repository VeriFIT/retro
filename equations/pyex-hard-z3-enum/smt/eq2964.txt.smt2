(set-logic QF_S)
(declare-fun V27 () String )
(declare-fun V20 () String )
(declare-fun V46 () String )
(declare-fun V16 () String )
(declare-fun V37 () String )
(declare-fun V45 () String )
(declare-fun V49 () String )
(declare-fun V38 () String )
(declare-fun V11 () String )
(declare-fun V15 () String )
(declare-fun V9 () String )
(declare-fun V10 () String )
(declare-fun V28 () String )
(declare-fun V36 () String )
(declare-fun V13 () String )
(declare-fun V41 () String )
(declare-fun V48 () String )
(declare-fun V7 () String )
(declare-fun V33 () String )
(declare-fun V42 () String )
(declare-fun V25 () String )
(declare-fun V4 () String )
(declare-fun V2 () String )
(declare-fun V19 () String )
(declare-fun V0 () String )
(declare-fun V44 () String )
(declare-fun V52 () String )
(declare-fun V39 () String )
(declare-fun V47 () String )
(declare-fun V51 () String )
(declare-fun V3 () String )
(declare-fun V24 () String )
(declare-fun V29 () String )
(declare-fun V26 () String )
(declare-fun V40 () String )
(declare-fun V6 () String )
(declare-fun V21 () String )
(declare-fun V34 () String )
(declare-fun V14 () String )
(declare-fun V8 () String )
(declare-fun V23 () String )
(declare-fun V30 () String )
(declare-fun V12 () String )
(declare-fun V5 () String )
(declare-fun V31 () String )
(declare-fun V35 () String )
(declare-fun V32 () String )
(declare-fun V22 () String )
(declare-fun V43 () String )
(declare-fun V50 () String )
(declare-fun V1 () String )
(declare-fun V17 () String )
(declare-fun V18 () String )
(assert (= "" V14 ) )
(assert (= "/" V0 ) )
(assert (= ":" V16 ) )
(assert (= "W" V8 ) )
(assert (= "Z" V11 ) )
(assert (= V21 (str.++ (str.++ V28 V29 ) V30 ) ) )
(assert (= V2 (str.++ (str.++ V36 "@" ) V37 ) ) )
(assert (= V2 (str.++ (str.++ V48 "Z" ) V49 ) ) )
(assert (= V2 (str.++ (str.++ V23 V24 ) V25 ) ) )
(assert (= V2 (str.++ (str.++ V43 V44 ) V25 ) ) )
(assert (= V2 (str.++ (str.++ V5 V9 ) V10 ) ) )
(assert (= V2 (str.++ (str.++ V5 V12 ) V13 ) ) )
(assert (= V2 (str.++ (str.++ V5 V14 ) V15 ) ) )
(assert (= V2 (str.++ (str.++ V5 V6 ) V7 ) ) )
(assert (= V2 (str.++ (str.++ V26 V27 ) V25 ) ) )
(assert (= V23 V5 ) )
(assert (= V47 (str.++ "w" V9 ) ) )
(assert (= V47 (str.++ (str.++ V45 "w" ) V46 ) ) )
(assert (= V52 (str.++ (str.++ V50 "z" ) V51 ) ) )
(assert (= V9 (str.++ (str.++ V45 "W" ) V46 ) ) )
(assert (= V12 (str.++ (str.++ V50 "Z" ) V51 ) ) )
(assert (= V6 (str.++ (str.++ V34 "@" ) V35 ) ) )
(assert (= V27 (str.++ (str.++ V31 V32 ) V33 ) ) )
(assert (= V4 (str.++ (str.++ V20 V21 ) V22 ) ) )
(assert (= V4 (str.++ (str.++ V38 "/" ) V39 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V19 (str.++ (str.++ V17 V4 ) V18 ) ) )
(assert (= V19 (str.++ (str.++ V41 "://" ) V42 ) ) )
(assert (= V19 (str.++ "mongodb://" V40 ) ) )
( check-sat )
