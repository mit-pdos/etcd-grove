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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]
variable [package_sem' : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **`MustUnmarshalMessage(um, data)`**, a case per message type. It panics unless the bytes
decode, so each case takes the bytes' decoding as a premise (the caller's: the entry's proposer
marshalled it).
* `ConfChange` (`&cc`, the bytes `bs` of a committed conf-change entry, the encoding of a
  `ConfChange`: `isConfChangeEncoding`, which `entriesFrom` states): `cc` holds some change,
  whose `Id` field holds the bytes' id, `ccIdOf bs` (2026-10-12, the request path's unit 2: the
  decoding is a function of the bytes; the apply loop's premise `entryWaitOk` names the id).
* `InternalRaftRequest` (`&raftReq`, the bytes of a committed normal entry, which decode to `rq`:
  `irrDecode`, opaque): the struct holds `rq` (`internalRaftRequestIs`, read-only from then on).
-/
abbrev pbutil.MustUnmarshalMessage.spec : Prop :=
  (∀ (cc : Loc) (v : raftpb.ConfChange) (d : GoSlice) (bs : List w8) (dq : DFrac),
  isConfChangeEncoding bs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ cc ↦ v ∗ d ↦*{dq} bs }}
    (App (App (Val (@! pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc))) (Val #d))
  {{ RET #(); (∃ v' : raftpb.ConfChange, cc ↦ v' ∗ optU64 v'.Id' (ccIdOf bs)) ∗
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
