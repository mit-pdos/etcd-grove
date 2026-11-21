/-
`getMsg(b)` (`examples/raft/kvnet/wire.go`): what `putMsg` wrote (`encMsg st`, `Wire.lean`), all of
`b`, read back: a fresh message holding `st` without its responses, owned, with its `Entries` slice's
capacity (`msgPtsC l 1 1 true`, what `copyMsg` gives and raft's `Step` takes), and `true`. Stated of
the bytes `putMsg` wrote, for a message `getMsg` reads back (`MsgWf`: a type raft has, entries and a
snapshot of Go slices' lengths).

**The premise `st.ents = [] ∨ st.snap = none`** (no raft message carries both: `MsgApp` entries,
`MsgSnap` a snapshot): the decoders this one calls disagree on the bytes' fraction -- `getEntry`
reads read-only bytes (`↦*□`: the entry's data aliases them, and an entry's data is read-only for
good) and `getSnapshot` owned ones (the snapshot's data aliases them, owned with the snapshot) --
and the entries come before the snapshot, each decoder taking the rest of the bytes after it. With
no entries the bytes stay owned for the snapshot; with no snapshot they are frozen for the entries.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Wire
public import KvNet.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev getMsg.spec : Prop :=
  ∀ (b : GoSlice) (st : MsgSt), MsgWf st → (st.ents = [] ∨ st.snap = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      b ↦* encMsg st }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMsg)) (Val #b))
  {{ (l : Loc), RET (PairV #l #true);
      msgPtsC l (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
