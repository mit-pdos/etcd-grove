/-
`pbutil.MustUnmarshalMessage(um, data)` (`pkg/v3/pbutil`, names-only): the trust boundary.
Lean-first (no Rocq counterpart). A case per message type the verified code unmarshals: a raft
`ConfChange` (the apply thread, `InvRaftpb.lean`) and an `InternalRaftRequest` (the apply
package's `apply.Apply`, `apply/InvRequest.lean`). Stated over the two message packages'
assumptions only (not a caller's), so that the server and the apply package both use it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvRequest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3 go_etcd_io.raft.v3 go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]
variable [package_sem' : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **`MustUnmarshalMessage(um, data)`**, a case per message type. It panics unless the bytes
decode, so each case takes the bytes' decoding as a premise (the caller's: the entry's proposer
marshalled it).
* `ConfChange` (`&cc`, the bytes `bs` of a committed conf-change entry, the encoding of a
  `ConfChange`: `isConfChangeEncoding`, which `entriesFrom` states): `cc` holds some change
  (raft's `ownCCV1`, owned: its cells, its context bytes read-only, its hidden fields in the
  `protobuf` invariant, as raft's `proto.Unmarshal` axiom hands a decoded message out), whose
  content is what raft's decoder makes of the bytes (`ccDecodeV1 bs = some m`; stage R8b of the
  raft v3.7 retarget, 2026-10-16: until then an opaque id `ccIdOf bs`, now the decoded `id`,
  `ccIdOf_of_decode`; 2026-10-12, the request path's unit 2: the decoding is a function of the
  bytes; the apply loop's premise `entryWaitOk` names the id). Until stage R6 of the retarget
  the struct value with its `Id` cell only (`optU64`), the shape the server's own getter spec
  read; raft's `GetId` reads `ownCCV1`.
* `InternalRaftRequest` (`&raftReq`, the bytes of a committed normal entry, which decode to `rq`:
  `irrDecode`, opaque): the struct holds `rq` (`internalRaftRequestIs`, read-only from then on).
-/
abbrev pbutil.MustUnmarshalMessage.spec : Prop :=
  (∀ (cc : Loc) (v : raftpb.ConfChange) (d : GoSlice) (bs : List w8) (dq : DFrac),
  isConfChangeEncoding bs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ cc ↦ v ∗ d ↦*{dq} bs }}
    (App (App (Val (@! pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc))) (Val #d))
  {{ RET #(); (∃ m : CCV1M, ownCCV1 cc (DFrac.own 1) m ∗ ⌜ccDecodeV1 bs = some m⌝) ∗
      d ↦*{dq} bs }}) ∧
  (∀ (p : Loc) (x : etcdserverpb.InternalRaftRequest) (d : GoSlice) (bs : List w8) (dq : DFrac)
    (rq : apply.IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ p ↦ x ∗ d ↦*{dq} bs ∗
      ⌜apply.irrDecode bs = some rq⌝ }}
    (App (App (Val (@! pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.InternalRaftRequest.ty) #p)))
      (Val #d))
  {{ RET #(); apply.internalRaftRequestIs p rq ∗ d ↦*{dq} bs }})

end spec

end EtcdGrove
end Perennial
