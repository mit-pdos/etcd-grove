/-
`UnsafeReadScheduledCompact` (`store.go`): the meta key `scheduledCompactRev` (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CmpRecs

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

/-- `UnsafeReadScheduledCompact(tx)` over a reader of the `Meta` bucket's compaction keys under the
optional record set `rs` (`metaReadSpecR`; M2, the storage side, 2026-10-30: review round 5's S1, the
approval's item 28, one spec in place of today's flag `nc` and the drafted `specR`): the main revision
read and `true`, or `0` and `false` (none); and, under records `some r`, exactly the record
(`r.sched`: found with its revision, or absent). At `none` (`metaReadSpec rt false`: a value the
store wrote, `RevToBytes(Revision{Main: x})`, `x ≥ 0`, which one is not modelled:
`checkPrevCompactionCompleted`'s reader) nothing more; at `some CmpRecs.empty` (`metaReadSpec rt
true`, the restore plan's R4c: a backend that records no compaction) `0` and `false`. Under the
reader's token `Tok`, the value's slice read through `rdCap` (the backend-compaction stage,
2026-10-29: the backend lends its slices). -/
abbrev mvcc.UnsafeReadScheduledCompact.spec : Prop :=
  ∀ (rt : GoInterfaceOk) (rs : Option mvcc.CmpRecs) (Rd : GoSlice → GoString → IProp GF)
    (Tok : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      □ mvcc.metaReadSpecR rt rs Rd Tok ∗ mvcc.rdCap Rd Tok ∗ Tok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact))
      (Val #(GoInterface.ok rt)))
  {{ (x : w64) (found : Bool), RET (PairV #x #found); Tok ∗
      ⌜(found = true → 0 ≤ sint.Z x) ∧ (found = false → x = W64 0) ∧
        ∀ r, rs = some r →
          (found = true ∧ r.sched = some x) ∨ (found = false ∧ r.sched = none ∧ x = W64 0)⌝ }}

end spec

end EtcdGrove
end Perennial
