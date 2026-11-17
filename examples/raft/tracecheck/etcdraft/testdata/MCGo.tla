---- MODULE MCGo ----
\* etcdraft.tla's NextDynamic from its Init, under bounds, for comparing its state space with the
\* Go transcription's (etcdraft_test.go, TestStateSpaceMatchesTLC): the same bounds there.
EXTENDS etcdraft

CONSTANTS MaxTerm, MaxLog, MaxMsgs, MaxReconfig

GoConstraint ==
    /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
    /\ BagCardinality(messages) + BagCardinality(pendingMessages) <= MaxMsgs
    /\ reconfigCount <= MaxReconfig

GoSpec == Init /\ [][NextDynamic]_vars
====
