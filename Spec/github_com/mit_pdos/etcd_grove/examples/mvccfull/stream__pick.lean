/- Lean-first (no Rocq counterpart).

`s.pick()` (`examples/mvccfull/mvccfull.go`), under `s.mu` (its invariant's body, `smuBody`,
`Streams.lean`): a registered watcher not marked cancelled, if any (`ok`), chosen with `choose`
among the order slice's. The lock's contents unchanged.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Streams

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev stream.pick.spec : Prop :=
  ∀ (T : Strm) (rs : List WResp) (W : GMap w64 Reg) (Hl : List HRev) (P : w64),
  {{ streamCtx (GF := GF) T ∗ smuBody T rs W Hl P }}
    (App (T.s @!! go.GoType.PointerType stream.ty @!! go!"pick") (Val #()))
  {{ (id : w64) (ok : Bool), RET (PairV #id #ok); smuBody T rs W Hl P ∗
      ⌜ok = true → ∃ x, W !! id = some x ∧ x.cm = false⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
