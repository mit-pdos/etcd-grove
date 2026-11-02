/-
Lemmas of the `MemoryStorage` proofs (raft v3.7 retarget, stage R3): reading the storage's entry
slice (`entsRO`, `InvPbLog.lean`) at a position (`LemmasEnts`, re-exported). U8 v2 step 3: the
conf-state lemma of the old `StorState` record (`confState_eq_storCS`) is gone with its fields.
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section
