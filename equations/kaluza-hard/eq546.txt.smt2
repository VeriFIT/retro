(set-logic QF_S)
(declare-fun V15 () String )
(declare-fun V4 () String )
(declare-fun V5 () String )
(declare-fun V10 () String )
(declare-fun V14 () String )
(declare-fun V19 () String )
(declare-fun V8 () String )
(declare-fun V18 () String )
(declare-fun V16 () String )
(declare-fun V20 () String )
(declare-fun V13 () String )
(declare-fun V12 () String )
(declare-fun V17 () String )
(declare-fun V7 () String )
(assert (= (str.++ (str.++ V7 "\x09" ) V8 ) (str.++ (str.++ V16 V17 ) V18 ) ) )
(assert (= (str.++ (str.++ V7 "\x09" ) V8 ) (str.++ (str.++ (str.++ V19 "\r" ) V20 ) V12 ) ) )
(assert (= (str.++ (str.++ V4 " " ) V5 ) (str.++ (str.++ V13 V14 ) V15 ) ) )
(assert (= (str.++ (str.++ V4 " " ) V5 ) (str.++ (str.++ (str.++ V7 "\x09" ) V8 ) V10 ) ) )
( check-sat )
