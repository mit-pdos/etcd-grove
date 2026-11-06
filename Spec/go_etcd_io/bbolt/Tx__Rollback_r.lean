/-
`Tx.Rollback_r` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U5; used by U10 (`freepages`), U11. Proof:
`Proof/go_etcd_io/bbolt/Tx__Rollback_r.lean` (a `sorry` until U5).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.Rollback()` of a whole reader (internal, any pair source; design §4.2 "reader
`Tx.Rollback`/`Tx.close` over `rdTx`"): nil; the transaction is done, and its pair source given
back (`pairBack`: the `threadTok` of a pool loan, or the spare pair). -/
abbrev Tx.Rollback_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (T : TxView) (v : View),
  {{ rdTxK (GF := GF) K tx src 1 T v }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ txDoneDef tx ∗ pairBack K src }}

end spec

end bbolt
end EtcdGrove
end Perennial
