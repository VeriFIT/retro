(set-logic QF_S)
(declare-fun V15 () String )
(declare-fun V27 () String )
(declare-fun V7 () String )
(declare-fun V11 () String )
(declare-fun V16 () String )
(declare-fun V1 () String )
(declare-fun V22 () String )
(declare-fun V21 () String )
(declare-fun V13 () String )
(declare-fun V25 () String )
(declare-fun V18 () String )
(declare-fun V8 () String )
(declare-fun V23 () String )
(declare-fun V6 () String )
(declare-fun V26 () String )
(declare-fun V20 () String )
(declare-fun V14 () String )
(declare-fun V12 () String )
(declare-fun V10 () String )
(declare-fun V24 () String )
(declare-fun V4 () String )
(declare-fun V17 () String )
(assert (= (str.++ V16 V17 ) (str.++ V14 V15 ) ) )
(assert (= (str.++ V16 V17 ) (str.++ "//" V4 ) ) )
(assert (= (str.++ V16 V17 ) (str.++ (str.++ V22 "/" ) V23 ) ) )
(assert (= (str.++ V16 V17 ) (str.++ (str.++ V6 V7 ) V8 ) ) )
(assert (= (str.++ V16 V17 ) (str.++ (str.++ V13 V10 ) V11 ) ) )
(assert (= (str.++ V16 V17 ) (str.++ (str.++ (str.++ V18 V24 ) "/" ) V25 ) ) )
(assert (= (str.++ (str.++ V24 "/" ) V25 ) (str.++ (str.++ V26 "/" ) V27 ) ) )
(assert (= (str.++ (str.++ V20 ":" ) V21 ) (str.++ (str.++ V1 V16 ) V17 ) ) )
(assert (= (str.++ (str.++ V20 ":" ) V21 ) (str.++ "http" V12 ) ) )
( check-sat )
