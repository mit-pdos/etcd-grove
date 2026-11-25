/-
The part's own `BootMarshal` (raft without hand-written axioms, `notes/raft-noax-part.md`): empty.

The main tree's `Proof/go_etcd_io/raft/v3/BootMarshal.lean` (premises to axioms, item B, 2026-11-24)
proves `bootMarshal` from the axiom `proto.MarshalBootConfChange.wp_proof` (`proto.Marshal` of a boot
conf change returns exactly `ccBootWire`'s bytes). This part's raft marshals with
`raftpb.MarshalConfChangeV1` (`raftpb/noax.go`), whose spec gives bytes that decode back to the
message (`ccDecodeV1`), not the bytes themselves, and the part takes no axiom: so `bootMarshal` (this
part's, over `MarshalConfChangeV1`) is not derived here, and nothing of the part needs it. The module
exists because `etc/api/raft.txt` lists the main tree's as importable (a root of `etc/copy-part.py`);
this file, without the copier's first line, keeps the copy out.
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.ApiVocab

@[expose] public section
