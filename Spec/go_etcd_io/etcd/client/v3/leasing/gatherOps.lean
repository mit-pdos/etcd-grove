/-
`gatherOps(ops)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`gatherOps(ops)`** for the operation trees `ts` (with the spare capacity of every nested
`thenOps` slice, owned: `append(thenOps, elseOps...)` writes `elseOps` into it, as the code does):
the plain operations, in order (`OpT.leavesL`), in a fresh slice. -/
abbrev gatherOps.spec : Prop :=
  ∀ (sl : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op) (ts : List OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ sl ↦*□ vs ∗ opListAtC true vs ts }}
    (App (Val (@! go_etcd_io.etcd.client.v3.leasing.gatherOps)) (Val #sl))
  {{ (ret : GoSlice), RET #ret; opsOwn ret (OpT.leavesL ts) ∗
      ⌜∀ o ∈ OpT.leavesL ts, o.t ≠ W64 4⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
