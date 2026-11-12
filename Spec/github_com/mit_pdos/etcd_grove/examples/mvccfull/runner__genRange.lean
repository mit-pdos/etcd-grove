/- Lean-first (no Rocq counterpart).

`x.genRange(cur, cmp)` (`examples/mvccfull/mvccfull.go`): a range read's request, its key and end
owned by the caller (`genKey`, `genEnd`), its options any of those the code makes: the revision
`0`, `-1`, `cmp`, or one in `[0, max 0 (cur + 1)]` (`choose(int(cur) + 2)`; `0` when the sum is not
positive, wrapped or not); a limit in `[0, len(keys) + 1]` (`choose(len + 2)`, likewise); any
count-only, keys-only and total-count flags. Reads `x.cfg.Mix.RangeRev` (`pick`, whose result only
selects among these). Used by the readers (at a transaction's revision and compaction revision, or
`revHi` and the floor `clo` for the store's own `Range`) and the writer's txns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev runner.genRange.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (cur cmp : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      runnerKeys x ks ∗ runnerRangeMix x cfg }}
    (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"genRange") (Val #cur)) (Val #cmp))
  {{ (q : rangeReq), RET #q; ∃ kk e : GoString, q.key' ↦* kk ∗ q.end' ↦* e ∗
      ⌜kk ∈ ks ∧ (e = [] ∨ e = go!"d" ∨ e ∈ ks)⌝ ∗
      ⌜(q.ro'.Rev' = W64 0 ∨ q.ro'.Rev' = W64 (-1) ∨ q.ro'.Rev' = cmp ∨
          (0 ≤ sint.Z q.ro'.Rev' ∧ sint.Z q.ro'.Rev' ≤ max 0 (sint.Z cur + 1))) ∧
        0 ≤ sint.Z q.ro'.Limit' ∧ sint.Z q.ro'.Limit' ≤ ks.length + 1⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
