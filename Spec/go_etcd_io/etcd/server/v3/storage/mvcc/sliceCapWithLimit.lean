/-
`sliceCapWithLimit` (`kvstore_txn.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `sliceCapWithLimit[S](limit, s)` is `capWithLimit limit (len s)` (for any element type
`S` represented by `V`). -/
abbrev mvcc.sliceCapWithLimit.spec : Prop :=
  ∀ {V : Type} (S : go.GoType) [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V S]
    (limit : w64) (s : GoSlice) (vs : List V) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ s ↦*{dq} vs }}
    (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.mvcc.sliceCapWithLimit [S]))
      (Val #limit)) (Val #s))
  {{ RET #(W64 (mvcc.capWithLimit limit vs.length)); s ↦*{dq} vs }}

end spec

end EtcdGrove
end Perennial
