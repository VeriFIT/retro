(set-logic QF_S)
(declare-fun V7 () String )
(declare-fun V3 () String )
(declare-fun V4 () String )
(declare-fun V9 () String )
(declare-fun V11 () String )
(declare-fun V12 () String )
(declare-fun V10 () String )
(declare-fun V8 () String )
(assert (= (str.++ (str.++ V3 "\r" ) V4 ) (str.++ (str.++ V8 V9 ) V10 ) ) )
(assert (= (str.++ (str.++ V3 "\r" ) V4 ) (str.++ (str.++ (str.++ V11 "\x09" ) V12 ) V7 ) ) )
( check-sat )
