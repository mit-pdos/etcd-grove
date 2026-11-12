/-
`tx.rollback()` of a writer, flagged (maintainer 11, for `Commit`'s and `commitFreelist`'s
rollbacks after `Commit`'s free of the synced freelist page): `Tx.rollback.spec` over `wtxEnd' fr`
(`wdbOK' fr` and the writer's `fbTok`). With `fr = true` the writer has not published, and the
freed page's slots come back holding its bytes (`store_rollback` through the token, `fbRel`).
Proof: `Proof/go_etcd_io/bbolt/Tx__rollback_f.lean` (with `Tx.rollback.spec_of_f`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackSpec
public import Proof.go_etcd_io.bbolt.Inv.WdbFlag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.rollback()` of a writer, flagged**: `Tx.rollback.spec` from `wtxEnd' fr`; with the flag
(after `Commit`'s free of the synced freelist page) the writer has not published. -/
abbrev Tx.rollback_f.spec : Prop :=
  ∀ [HasExt osFsExt] (fr : Bool) (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb),
  rbOK X ws w → (fr = true → ws.2.2.1 = false) →
  {{ wtxEnd' (GF := GF) fr K tx r X ws w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"rollback")) (Val #()))
  {{ RET #(); txDoneDef tx }}

end spec

end bbolt
end EtcdGrove
end Perennial
