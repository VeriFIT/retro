(set-logic QF_S)
(declare-fun V17 () String )
(declare-fun V14 () String )
(declare-fun V5 () String )
(declare-fun V10 () String )
(declare-fun V12 () String )
(declare-fun V8 () String )
(declare-fun V11 () String )
(declare-fun V4 () String )
(declare-fun V16 () String )
(declare-fun V13 () String )
(declare-fun V15 () String )
(assert (= (str.++ (str.++ V4 "\r" ) V5 ) (str.++ (str.++ V13 V14 ) V15 ) ) )
(assert (= (str.++ (str.++ V4 "\r" ) V5 ) (str.++ (str.++ (str.++ V16 "\f" ) V17 ) V10 ) ) )
(assert (= (str.++ (str.++ V11 "\f" ) V12 ) (str.++ (str.++ (str.++ V8 V4 ) "\r" ) V5 ) ) )
( check-sat )
