/-
`getMsgEntry(b)` (wire.go): what `putEntry` wrote at the start of `b` (`encEntry e`), an entry of a
message, of any type (`MsgEntWf`: only its data of a Go slice's length; `getEntry`, which reads a file,
refuses a type raft does not have), read back into a fresh entry (`entOwn`), the rest, and `ok`, as
`getEntry`'s spec (`getEntry.lean`): the bytes at any fraction, the entry's data frozen.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Wire
public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev getMsgEntry.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (e : EntryM) (r : List w8),
  MsgEntWf e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ b ↦*{dq} (encEntry e ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getMsgEntry)) (Val #b))
  {{ (l : Loc) (rest : GoSlice), RET (PairV (PairV #l #rest) #true);
      entOwn l e ∗ rest ↦*{dq} r }}

end spec

end kvraft
end EtcdGrove
end Perennial
