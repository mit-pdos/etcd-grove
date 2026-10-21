# Model checking the witness across reconfiguration

`model.py`: an explicit-state model of etcd-raft membership changes with one witness, as
raft#168 does it in the fork `raft-witness-goose-lean` (`9ed005d46`). It extends
`issues/raft-conf-lag-model/model.py` (atomic elections, one AppendEntries round trip per `app`,
apply-time configuration switching) with subterms, the leader's epoch (excluded voter per half),
the witness's storage (atomic CAS) and each node's proxy cache, the witness's vote and append
rules, `getWitnessVoteRequestReadiness`, `maybeCommit`'s quorum-1 index per replicating half,
`ChangeReplicationSet` (any member excluded: a superset of the code's choices),
`ResetReplicationSet` on a leader's `switchToConfig` when a witness is involved, and confchange's
witness rules (`AddWitness`, removing the witness, `EnterJoint` copying `Witnesses[0]` to `[1]`,
`LeaveJoint` clearing `[1]`). The header of `model.py` lists what is modelled and its flags.

Checked: state machine safety (committed prefixes agree), leader completeness at each win,
election safety.

    REDUCED=1 python3 model.py NREG INIT MODE MAXT MAXLOG MAXCONF MAXVAL [flags]   # BFS
    WALKS=5000 SEED=1 MAXLEN=80 python3 model.py ...                               # random walks
    REPLAY=trace.txt python3 model.py ...                                           # a trace

`REDUCED=1` lets `app` send at most one entry past the common prefix (as `model.py`).

Runs and results: `notes/raft-witness-reconfig.md`; logs in `runs/`.
