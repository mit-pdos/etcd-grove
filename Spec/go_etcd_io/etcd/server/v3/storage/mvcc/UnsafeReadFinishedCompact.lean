/-
`UnsafeReadFinishedCompact` (`store.go`): the meta key `finishedCompactRev` (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `UnsafeReadFinishedCompact(tx)` over a reader of the `Meta` bucket's compaction keys (`metaReadSpec`: what the
store wrote there, `RevToBytes(Revision{Main: x})`, `x ≥ 0`; which one is not modelled): the main
revision read and `true`, or `0` and `false` (none); over a reader that finds nothing (`nc`:
the restore plan's R4c), `0` and `false`. Under the reader's token `Tok`, the value's slice read
through `rdCap` (the backend-compaction stage, 2026-10-29: the backend lends its slices). -/
abbrev mvcc.UnsafeReadFinishedCompact.spec : Prop :=
  ∀ (rt : GoInterfaceOk) (nc : Bool) (Rd : GoSlice → GoString → IProp GF) (Tok : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ mvcc.metaReadSpec rt nc Rd Tok ∗ mvcc.rdCap Rd Tok ∗ Tok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact)) (Val #(GoInterface.ok rt)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); Tok ∗
      ⌜(found = true → 0 ≤ sint.Z x) ∧ (found = false → x = W64 0) ∧
        (nc = true → found = false)⌝ }}

end spec

end EtcdGrove
end Perennial
