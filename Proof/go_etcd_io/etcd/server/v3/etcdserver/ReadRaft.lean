/-
**The read loop's `raftInterface` contract, met by the server's raft wrapper** (`isReadRaft`,
`read/Inv.lean`; the request path's unit 4b, 2026-10-13): from the wrapper's persistent view
(`isRaftNode E γ r`, whose node contract carries `ReadIndex` and the `Ready`'s read states, at the
read names `E.γr` and the registrations `E.RQ`) and the specs of `ReadState` and `ReadIndex`, the
`*raftNode` value `r` meets the contract the read loop is verified over. Lean-first (no Rocq
counterpart); mirrors how the request path's `raftPropose` is a contract on the node.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__ReadState
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__ReadIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The raft wrapper meets the read loop's `raftInterface` contract** (see the file header). -/
theorem isReadRaft_of_raftNode
    (hRS : raftNode.ReadState.spec (GF := GF) (hG := hG))
    (hRI : raftNode.ReadIndex.spec (GF := GF) (hG := hG))
    (E : RNEnv GF) (γ : RNNames) (r : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ⊢
      isReadRaft (interface.mkOk (go.GoType.PointerType raftNode.ty) #r) E.γr E.RQ := by
  iintro ⟨#Hpkg, #Hr⟩
  iunfold isReadRaft
  iexists ⟨go.GoType.PointerType raftNode.ty, #r⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply hRS E γ r $$ [] as %c #Hc
    · iframe #
    iapply HΦ
    iunfold isRNReadStateC at Hc
    iexact Hc
  · iintro !> %ctx %cd %sl %dq %id %n %Φ !> ⟨#Hctx, Hsl, #Hc⟩ HΦ
    wp_apply hRI E γ r ctx cd sl dq id n $$ [Hsl] as %err Hpost
    · iframe #; iframe Hsl
    iapply HΦ
    iexact Hpost

end proof

end EtcdGrove
end Perennial
