/-
The part's own `MarshalBootConfChange` (raft without hand-written axioms, `notes/raft-noax-part.md`):
empty, as the part's `BootMarshal.lean`.

The main tree's `Spec/google_golang_org/protobuf/proto/MarshalBootConfChange.lean` states
`proto.Marshal`'s bytes of a boot conf change as `ccBootWire` (`Proof/go_etcd_io/raft/v3/CCModel.lean`,
since 2026-11-25; until then in `BootWire.lean`, which no part's `CCModel` clashed with). This part's
`CCModel` is its own (the noax decoder) and has no `ccBootWire`, and this part takes no axiom, so it
has no use for the spec: nothing of the part imports it. This file, without the copier's first line,
keeps the copy out.
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.ApiVocab

@[expose] public section
