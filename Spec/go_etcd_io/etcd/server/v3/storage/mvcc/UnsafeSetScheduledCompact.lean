/-
`UnsafeSetScheduledCompact` (`store.go`) (2026-10-13, unit 5a).
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

/-- `UnsafeSetScheduledCompact(tx, value)`, `value ≥ 0`: its `UnsafePut` of
`RevToBytes(Revision{Main: value})` at the compaction key, through a capability to put a compaction
key into `Meta` from the token `X` to `Y` (`metaPutCap`; the backend-compaction stage, review round
2, R2-3: a fresh session's lock to an `Unlock`-only token, `SetScheduledCompact`'s, or a step of a
compacting range's token, the job's; until then `Locked l` of mvcc's assumed backend). The store's
record of the key (`metaCompact`) is its own: the caller updates it. -/
abbrev mvcc.UnsafeSetScheduledCompact.spec : Prop :=
  ∀ (bt : GoInterfaceOk) (X Y : IProp GF) (value : w64),
  0 ≤ sint.Z value →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.metaPutCap bt X Y ∗ X }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetScheduledCompact)) (Val #(GoInterface.ok bt)))
      (Val #value))
  {{ RET #(); Y }}

end spec

end EtcdGrove
end Perennial
