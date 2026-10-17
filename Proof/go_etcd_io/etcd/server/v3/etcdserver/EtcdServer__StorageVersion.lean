/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__StorageVersion.lean` (etcd PR
#22190's verification). Lean-first; see `InvBackendLife.lean`.

Under `bemu`'s read lock, the lock's resource holds a fraction of the backend's open token or the
backend shut with `stopping` closed. Shut: the non-blocking receive on `stopping` is ready (its done
view), so `nil` is returned without reading the backend. Open: whatever the receive does, the
fraction is there for `DetectSchemaVersion`. (Without the PR's `select`, the shut case has no open
token for `DetectSchemaVersion`: the proof does not go through, which is the bug the PR fixes.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__StorageVersion
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.DetectSchemaVersion
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3
  go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [package_sem_schema : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

set_option hygiene false in
/-- The receive is ready: `return nil`, the deferred `RUnlock` (the lock's resource as taken). -/
local macro "sv_ret_nil" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [Hlk Hb Hok Hst2] as Hrd
  · iframe Hlk; inext; iunfold bemuP; iexists b; iframe Hb Hok Hst2
  (try wp_auto)
  iapply HΦ
  isplitl [Hrd]
  · iunfold srvBemuReader; iexists L; iexact Hrd
  iframe Hst
  isplitr
  · ipureintro; intro _; rfl
  ileft; ipureintro; rfl))

set_option hygiene false in
/-- The receive is not ready, the backend open (`HO`): `DetectSchemaVersion` over the backend's
read transaction with the open token's fraction, the error's warning, the deferred `RUnlock`. -/
local macro "sv_read" : tactic => `(tactic| (
  (try wp_auto)
  ihave #Hok' := Hok
  iunfold beLifeOk at Hok'
  icases Hok' with ⟨-, %bi, %Hbi, #HReadTx, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HReadTx as %rt #Hrt
  (try wp_auto)
  wp_apply hD l rt L.O sync.rfrac $$ [HO] as %sv %err HO
  · iframe Hrt HO
  (try wp_auto)
  cases err with
  | ok ei =>
    -- the error: warn, `nil`
    (try wp_auto)
    wp_apply hE (GoInterface.ok ei) $$ [] as %f -
    wp_apply wp_slice_literal (l := [f])
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    (try wp_auto)
    wp_apply hW l _ _ $$ []
    · ipureintro; exact Hlnn
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [Hlk Hb Hok HO] as Hrd
    · iframe Hlk; inext; iunfold bemuP; iexists (GoInterface.ok bi); iframe Hb Hok; ileft; iexact HO
    (try wp_auto)
    iapply HΦ
    isplitl [Hrd]
    · iunfold srvBemuReader; iexists L; iexact Hrd
    iframe Hst
    isplitr
    · ipureintro; intro _; rfl
    ileft; ipureintro; rfl
  | nil =>
    -- no error: `&v`
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [Hlk Hb Hok HO] as Hrd
    · iframe Hlk; inext; iunfold bemuP; iexists (GoInterface.ok bi); iframe Hb Hok; ileft; iexact HO
    (try wp_auto)
    iapply HΦ
    isplitl [Hrd]
    · iunfold srvBemuReader; iexists L; iexact Hrd
    iframe Hst
    isplitr
    · ipureintro; intro hcl; cases hcl
    iright; iexists _; iframe))

/-- A non-blocking receive on `stopping` (a `select` with a `default`) with an unknown view of
it: either the receive's handler or the default runs, over the same resources. -/
theorem wp_select_stopping (ch : Loc) (γ : ChanNames) (h dflt : Expr) (Φ : val → IProp GF) :
    ⊢ ownStopChan ch γ iprop(True) .Unknown -∗
      (WP (App h (Val (PairV #() #false))) {{ Φ }} ∧ WP dflt {{ Φ }}) -∗
      WP (App (Val (GoInstruction SelectStmt))
        (Val (SelectStmtClausesV (some dflt)
          [CommClause (RecvCase (go.GoType.StructType []) (Val #ch)) h]))) {{ Φ }} := by
  iintro #HU HW
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
    iprop(WP (App h (Val (PairV #() #false))) {{ Φ }} ∧ WP dflt {{ Φ }}) $$ [] [HW] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro HW
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ HU
    iapply stop_chan_nonblocking_receive ch γ iprop(True) _ _ .Unknown $$ HU
    isplit
    · iintro -
      icases HW with ⟨HW, -⟩
      iexact HW
    · iintro -
      iframe HW
  · iexact HW
  · iintro HW -
    icases HW with ⟨-, HW⟩
    iexact HW

set_option hygiene false in
/-- `stopping` known closed (the done view `Hd` at names `γ'`): the receive is ready. -/
local macro "sv_select_done" : tactic => `(tactic| (
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)] iprop(True)
    $$ [HΦ Hlk Hb Hst Hst2 defer s] [] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro -
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ'
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hd
    iapply stop_chan_nonblocking_receive ch γ' iprop(True) _ _ .Done $$ Hd
    isplit
    · iintro -
      sv_ret_nil
    · itrivial
  · iintro Hnr
    icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hf
    iexfalso; iexact Hf))

set_option hygiene false in
/-- The backend open (`HO`), `stopping`'s view unknown (`HU`): the receive's handler returns
`nil`, the default reads the backend. -/
local macro "sv_select_unknown" : tactic => `(tactic| (
  wp_apply_core wp_select_stopping ch γ _ _ _ $$ HU
  isplit
  · ihave Hst2 : iprop(L.O sync.rfrac ∨ beShut s L) $$ [HO]
    · ileft; iexact HO
    sv_ret_nil
  · sv_read))

theorem EtcdServer.StorageVersion.wp_proof
    (hD : schema.DetectSchemaVersion.spec (GF := GF) (hG := hG))
    (hE : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.StorageVersion.spec (GF := GF) (hG := hG) := by
  intro s l ch γ cl
  wp_start as ⟨Hrd, #Hlg, %Hlnn, #Hch, Hst⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvBemuReader at Hrd
  icases Hrd with ⟨%L, Hrd⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (lc := 1) sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  imod lc_fupd_elim_later $$ Hlc1 HP with HP
  iunfold bemuP at HP
  icases HP with ⟨%b, Hb, #Hok, Hst2⟩
  (try wp_auto)
  icases Hst2 with (HO | #Hshut)
  · -- the backend open
    cases cl
    · -- the caller is the closer (`.Pending`): an unknown view besides
      icases ownStopChan_pending_unknown ch γ iprop(True) $$ Hst with ⟨Hst, #HU⟩
      sv_select_unknown
    · -- the caller knows `stopping` closed: the receive is ready
      icases Hst with #Hd
      ihave Hst : ownStopChan ch γ iprop(True) .Done $$ []
      · iexact Hd
      ihave Hst2 : iprop(L.O sync.rfrac ∨ beShut s L) $$ [HO]
      · ileft; iexact HO
      generalize hγ' : γ = γ'
      rw [hγ'] at *
      sv_select_done
    · -- an unknown view
      icases Hst with #HU
      ihave Hst : ownStopChan ch γ iprop(True) .Unknown $$ []
      · iexact HU
      sv_select_unknown
  · -- the backend shut: `stopping` closed, the receive is ready
    ihave #Hshut' := Hshut
    iunfold beShut at Hshut'
    icases Hshut' with ⟨-, %ch', %γ', #Hch', #Hd⟩
    icombine Hch Hch' gives %Heq
    subst Heq
    ihave Hst2 : iprop(L.O sync.rfrac ∨ beShut s L) $$ [Hshut]
    · iright; iexact Hshut
    sv_select_done

end proof

end EtcdGrove
end Perennial
