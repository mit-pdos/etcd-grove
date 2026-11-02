/- `MemoryStorage.Append` (`storage.go:300`).

U8 v2 step 3 (2026-10-29): over the range vocabulary at the storage's names (`InvMemstorage.lean`;
`notes/raft-unified-plan.md`, "U8 v2"). Takes the range from the batch's first index `k` to the end (`own 1`) and the end, gives the batch as that range. The batch's indices are consecutive from `k`, its last at most `2^61` (the contract's `Hlen`, kept in the range). An empty batch is a no-op. -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.Append(entries)` at `k`, the first entry's index. (raft-final, 2026-10-29, the design's A4,
review 1's M2) An empty batch takes no range of the log (Go returns before the lock,
`storage.go:293-296`): a `Ready` with no entries lends none; until then the range from `k` with the
end in both cases. -/
abbrev MemoryStorage.Append.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (k : Nat) (old es : List EntryM) (s : GoSlice) (dq : DFrac),
  (∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j) →
  k + es.length ≤ 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) ∗
      entsPts s dq es }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #s))
  {{ RET #interface.nil; entsPts s dq es ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) }}

end spec

end EtcdGrove
end Perennial
