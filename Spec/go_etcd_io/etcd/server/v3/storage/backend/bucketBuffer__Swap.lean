/-
`bucketBuffer.Swap` (`tx_buffer.go`). `bb.Swap(i, j)` (`sort.Interface`): the two entries exchanged.
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `bb.Swap(i, j)` (`sort.Interface`): the two entries exchanged. -/
abbrev backend.bucketBuffer.Swap.spec : Prop :=
  ∀ (bb : Loc) (es : List Ent) (i j : w64) (a b : Ent),
  0 ≤ sint.Z i → 0 ≤ sint.Z j → es[sint.nat i]? = some a → es[sint.nat j]? = some b →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ ownBB bb es }}
    (App (App (Val (bb @!! go.GoType.PointerType bucketBuffer.ty @!! go!"Swap")) (Val #i)) (Val #j))
  {{ RET #(); ownBB bb ((es.set (sint.nat i) b).set (sint.nat j) a) }}

end spec

end EtcdGrove
end Perennial
