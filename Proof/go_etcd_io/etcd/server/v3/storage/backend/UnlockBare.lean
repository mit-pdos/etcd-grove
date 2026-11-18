/-
**`batchTxBuffered.Unlock` in the client-facing mode** (`Unlock.spec_free`: no claimed bucket, A1.8 of
`auth-schema-srv`), and **without a part of the tracked buckets** (decision 3 of
`notes/backend-auth-split-plan.md`, Q3): the statement as it was before `Unlock` took a part to make
idle, for the callers that hand it none, and its derivation from the restated spec (the empty bucket
set).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

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

/-- **`t.Unlock()` in the client-facing mode** (A1.8: `Unlock.spec` at no claimed bucket, `Sc = []`, `Rr = True`;
the mode weakened by `batchLocked_claimed`, no claimed write recorded by `cwOk`): what `Unlock.spec` said
before A1.5, for the callers that claim nothing. -/
theorem backend.batchTxBuffered.Unlock.spec_free
    (h : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG)) :
    ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF)
      (S : GoString → Prop) (r : GMap GoString BktData),
    st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
        bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗ rbPart γ S r ∗
        ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
           ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
         (∃ vd : VData, ⌜sbKept P st⌝ ∗ bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
      (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); Q ∗ rbOwnIn γ S r }} := by
  intro γ P W Pk b t st Q S r Hhw Hroom
  iintro %Φ ⟨#Hpkg, #Hb, #Ht, Hl, Htok, Hrb, Hcase⟩ HΦ
  icases batchLocked_cwOk γ P b st false $$ Hl with ⟨Hl, %Hcw⟩
  ihave Hl := batchLocked_claimed γ P b st $$ Hl
  ihave Hrc := rbPartR_nil (hG := hG) γ (∅ : GMap GoString BktData)
  ihave #Hacc := rbAcc_nil (hG := hG) γ (unlockOk P st) iprop(True) ⊤
  iapply (h γ P W Pk b t st Q S r [] ∅ iprop(True) ⊤ CoPset.subseteq_top Hhw Hroom List.nodup_nil
    (fun n h => by rw [Hcw rfl Hhw n] at h; cases h)) $$ %Φ [Hl Htok Hrb Hrc Hcase]
  · iframe Hl Htok Hrb Hrc Hcase; iframe #
  inext
  iintro ⟨HQ, Hin, -, -⟩
  iapply HΦ
  iframe HQ Hin

/-- `t.Unlock()` handed no part of the tracked buckets (`Unlock.spec_free` at the empty
bucket set): what its callers that need no idle part use. -/
abbrev backend.batchTxBuffered.Unlock.specBare : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, ⌜sbKept P st⌝ ∗ bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
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
  iapply (backend.batchTxBuffered.Unlock.spec_free h γ P W Pk b t st Q (fun _ => False) ∅ h1 h2) $$ %Φ [Hl Hwb Hbr Hn]
  · iframe Hl Hwb Hbr Hn; iframe #
  inext
  iintro ⟨HQ, -⟩
  iapply HΦ
  iexact HQ

end bare

end EtcdGrove
end Perennial
