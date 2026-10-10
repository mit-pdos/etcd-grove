/-
`concurrency.stm.Put(key, val, opts...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.Put(k, v, opts...)`: the write set gets the put of `k` (options a put supports). -/
abbrev stm.Put.spec : Prop :=
  ∀ (b : Loc) (pfx : GoString) (writes : GMap GoString WriteM) (k v : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmWsetOwn pfx b writes ∗ optsAt sl gs ∗ ⌜pfx <+: k ∧ PutOptsOk k v gs⌝ }}
    (App (App (App (Val (b @!! go.GoType.PointerType stm.ty @!! go!"Put")) (Val #k)) (Val #v))
      (Val #sl))
  {{ RET #(); stmWsetOwn pfx b (GMap.insert k (.put v (opPutModel k v gs).leaseID) writes) }}

end spec

end concurrency
end EtcdGrove
end Perennial
