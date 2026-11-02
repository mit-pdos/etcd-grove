/-
**`batchTxBuffered.Unlock` without a part of the tracked buckets** (decision 3 of
`notes/backend-auth-split-plan.md`, Q3): the statement as it was before `Unlock` took a part to make
idle, for the callers that hand it none, and its derivation from the restated spec (the empty bucket
set).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section bare
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.Unlock()` handed no part of the tracked buckets (`batchTxBuffered.Unlock.spec` at the empty
bucket set): what its callers that need no idle part use. -/
abbrev backend.batchTxBuffered.Unlock.specBare : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

/-- **`Unlock` handed no part** (the empty bucket set). -/
theorem backend.batchTxBuffered.Unlock.bare
    (h : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.Unlock.specBare (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st Q h1 h2
  iintro %Φ ⟨#Hpkg, #Hb, #Ht, Hl, Hwb, Hbr⟩ HΦ
  ihave Hn : rbPart (GF := GF) γ (fun _ => False) (∅ : GMap GoString BktData) $$ []
  · iapply rbPart_none
  iapply (h γ P W Pk b t st Q (fun _ => False) ∅ h1 h2) $$ %Φ [Hl Hwb Hbr Hn]
  · iframe Hl Hwb Hbr Hn; iframe #
  inext
  iintro ⟨HQ, -⟩
  iapply HΦ
  iexact HQ

end bare

end EtcdGrove
end Perennial
