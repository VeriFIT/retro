(set-logic QF_S)
(declare-fun V2 () String )
(declare-fun V38 () String )
(declare-fun V8 () String )
(declare-fun V43 () String )
(declare-fun V12 () String )
(declare-fun V20 () String )
(declare-fun V30 () String )
(declare-fun V51 () String )
(declare-fun V22 () String )
(declare-fun V40 () String )
(declare-fun V29 () String )
(declare-fun V39 () String )
(declare-fun V52 () String )
(declare-fun V47 () String )
(declare-fun V5 () String )
(declare-fun V13 () String )
(declare-fun V44 () String )
(declare-fun V41 () String )
(declare-fun V50 () String )
(declare-fun V55 () String )
(declare-fun V60 () String )
(declare-fun V59 () String )
(declare-fun V1 () String )
(declare-fun V28 () String )
(declare-fun V56 () String )
(declare-fun V11 () String )
(declare-fun V4 () String )
(declare-fun V34 () String )
(declare-fun V31 () String )
(declare-fun V45 () String )
(declare-fun V23 () String )
(declare-fun V49 () String )
(declare-fun V0 () String )
(declare-fun V54 () String )
(declare-fun V36 () String )
(declare-fun V16 () String )
(declare-fun V37 () String )
(declare-fun V53 () String )
(declare-fun V14 () String )
(declare-fun V32 () String )
(declare-fun V21 () String )
(declare-fun V26 () String )
(declare-fun V48 () String )
(declare-fun V35 () String )
(declare-fun V46 () String )
(declare-fun V24 () String )
(declare-fun V42 () String )
(declare-fun V27 () String )
(declare-fun V25 () String )
(declare-fun V15 () String )
(declare-fun V17 () String )
(declare-fun V18 () String )
(declare-fun V9 () String )
(declare-fun V3 () String )
(declare-fun V33 () String )
(declare-fun V7 () String )
(declare-fun V10 () String )
(declare-fun V19 () String )
(declare-fun V6 () String )
(assert (= "" V17 ) )
(assert (= "/" V0 ) )
(assert (= ":" V5 ) )
(assert (= "V" V16 ) )
(assert (= "Z" V10 ) )
(assert (= V2 (str.++ (str.++ V40 "@" ) V41 ) ) )
(assert (= V2 (str.++ (str.++ V51 "V" ) V52 ) ) )
(assert (= V2 (str.++ (str.++ V47 V22 ) V27 ) ) )
(assert (= V2 (str.++ (str.++ V48 V49 ) V27 ) ) )
(assert (= V2 (str.++ (str.++ V11 V17 ) V18 ) ) )
(assert (= V2 (str.++ (str.++ V11 V12 ) V13 ) ) )
(assert (= V2 (str.++ (str.++ V11 V14 ) V15 ) ) )
(assert (= V2 (str.++ (str.++ V30 V31 ) V27 ) ) )
(assert (= V2 (str.++ (str.++ V28 V29 ) V27 ) ) )
(assert (= V2 (str.++ (str.++ V32 V33 ) V27 ) ) )
(assert (= V2 (str.++ (str.++ V26 V9 ) V27 ) ) )
(assert (= V47 V32 ) )
(assert (= V48 V11 ) )
(assert (= V18 V27 ) )
(assert (= V50 V17 ) )
(assert (= V56 V12 ) )
(assert (= V22 V33 ) )
(assert (= V22 (str.++ (str.++ V37 V38 ) V39 ) ) )
(assert (= V22 (str.++ (str.++ V19 V20 ) V21 ) ) )
(assert (= V49 V17 ) )
(assert (= V9 (str.++ (str.++ V53 ":" ) V54 ) ) )
(assert (= V9 (str.++ (str.++ V6 V7 ) V8 ) ) )
(assert (= V37 V19 ) )
(assert (= V21 V39 ) )
(assert (= V55 V20 ) )
(assert (= V55 (str.++ (str.++ V59 "v" ) V60 ) ) )
(assert (= V38 V20 ) )
(assert (= V4 (str.++ (str.++ V34 V35 ) V36 ) ) )
(assert (= V4 (str.++ (str.++ V42 "/" ) V43 ) ) )
(assert (= V4 (str.++ (str.++ V1 V2 ) V3 ) ) )
(assert (= V25 (str.++ (str.++ V23 V4 ) V24 ) ) )
(assert (= V25 (str.++ (str.++ V45 "://" ) V46 ) ) )
(assert (= V25 (str.++ "mongodb://" V44 ) ) )
(assert (= (str.++ V47 V22 ) (str.++ V32 V33 ) ) )
(assert (= (str.++ V48 V49 ) (str.++ V11 V17 ) ) )
(assert (= (str.++ V22 V27 ) (str.++ V33 V27 ) ) )
(assert (= (str.++ V49 V27 ) (str.++ V17 V18 ) ) )
(assert (= (str.++ V37 V38 ) (str.++ V19 V20 ) ) )
(assert (= (str.++ V38 V39 ) (str.++ V20 V21 ) ) )
( check-sat )
