/-
`kvHashIncludes` (`hash.go`, the fork's split of `kvHasher.WriteKeyValue`'s filter, with
etcd-io/etcd#22515's `exactKeep`; pr-verify/etcd-22515): whether the hasher hashes a pair of the
`Key` bucket (`HashFilter.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashFilter
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RevBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `kvHashIncludes(c, rev, keep, exactKeep, k)`, of a bucket key `k` of revision `r` (a tombstone
when `k` ends in the mark) and a kept set `keep` (read at a fraction, given back), returns whether
the hasher at revision `rev` with compaction revision `c` hashes the pair: `hashInclF` with the
flag `exactKeep || len(keep) > 0` (at or below `rev`; at or below `c` only if `keep` keeps it,
when the flag is set; not a tombstone at `c`). `c + 1` and `rev + 1` do not overflow (`c` is a
compaction revision, at least `-1`). -/
abbrev mvcc.kvHashIncludes.spec : Prop :=
  ∀ (c rev : w64) (keep : GoMap) (dq : DFrac) (A : GMap Revision Unit) (exact : Bool)
    (s : GoSlice) (r : mvcc.Rev) (rest : List w8) (dk : DFrac),
  rest.length ≤ 1 → 0 ≤ sint.Z r.main → 0 ≤ sint.Z r.sub →
  -1 ≤ sint.Z c → sint.Z c < 2 ^ 63 - 1 → sint.Z rev < 2 ^ 63 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ownMap keep dq A ∗ s ↦*{dk} (mvcc.revBytes r false ++ rest) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.kvHashIncludes)) (Val #c))
      (Val #rev)) (Val #keep)) (Val #exact)) (Val #s))
  {{ RET #(decide (mvcc.hashInclF (sint.Z c) (sint.Z rev) (mvcc.keptBy A)
        (exact || decide (0 < GMap.size A)) r (decide (rest = [mvcc.markTomb]))));
      ownMap keep dq A ∗ s ↦*{dk} (mvcc.revBytes r false ++ rest) }}

end spec

end EtcdGrove
end Perennial
