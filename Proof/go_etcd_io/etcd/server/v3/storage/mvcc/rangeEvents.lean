/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.rangeEvents
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvsToEvents
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

set_option maxHeartbeats 4000000 in
theorem mvcc.rangeEvents.wp_proof
    (hNew : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (hRevTo : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (hKvs : mvcc.kvsToEvents.spec (GF := GF) (hG := hG)) :
    mvcc.rangeEvents.spec (GF := GF) (hG := hG) := by
  intro lg b γ Wr P f q log minRev maxRev g W
  wp_start as ⟨#Hbk, Hview, #Hcert, Hg, %Hrng⟩
  ihave %Hwf : ⌜mvcc.LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝ $$ [Hcert]
  · iunfold mvcc.idxCert at Hcert
    icases Hcert with ⟨-, -, %H, -⟩
    ipureintro; exact H
  iunfold mvcc.isKeyBackend at Hbk
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, #HR, -, -⟩
  subst Hbi
  wp_auto
  have hneg : ¬ sint.Z minRev < sint.Z (W64 0) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega
  rw [decide_eq_false hneg]
  wp_auto
  wp_apply hNew as %mn ⟨Hmn, Hmncap, -⟩
  wp_apply hNew as %mx ⟨Hmx, Hmxcap, -⟩
  (try wp_auto)
  wp_apply (hRevTo _ mn _ (Or.inl (by simp))) $$ [$Hmn $Hmncap] as %mn' ⟨Hmn, Hmncap⟩
  (try wp_auto)
  wp_apply (hRevTo _ mx _ (Or.inl (by simp))) $$ [$Hmx $Hmxcap] as %mx' ⟨Hmx, Hmxcap⟩
  (try wp_auto)
  simp only [List.drop_of_length_le (show (List.replicate 17 (W8 0)).length ≤ 17 by simp),
    List.append_nil, mvcc.revOf]
  wp_apply HR $$ [$Hview] as %rt ⟨Hview, Hsnap⟩
  icases Hsnap with ⟨%L, HL, #Hsnap⟩
  iunfold mvcc.keyReadSnap at Hsnap
  (try wp_auto)
  wp_bind (App (Val #(methods rt.ty go!"RLock" rt.v)) _)
  iapply Hsnap $$ %q [HL Hview]
  · iframe HL Hview
  inext
  iintro ⟨Hview, %Rd, %Tok, Htok, #Hlk⟩
  iunfold mvcc.keyReadLocked at Hlk
  icases Hlk with ⟨#HRU, -, #Hrange, #Hrc⟩
  (try wp_auto)
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩⟩
  iunfold mvcc.keyRangeReadSpec at Hrange
  ihave HRg := Hrange $$ %bK %mn' %mx'
  (try wp_auto)
  wp_apply HRg $$ [$HKeyG $Htok $Hmn $Hmx] as %ks %vs ⟨Htok, Hmn, Hmx, #Hkv⟩
  · ipureintro; simp [mvcc.revBytes]
  (try wp_auto)
  obtain ⟨hwf, hlen, hcs⟩ := Hwf
  have h1 : 0 ≤ sint.Z maxRev := by omega
  have hlo : sint.nat minRev ≤ sint.nat maxRev := by unfold sint.nat; unfold sint.Z at *; omega
  have hhi : sint.nat maxRev ≤ log.length := by unfold sint.nat; unfold sint.Z at *; omega
  have hbr : mvcc.bucketRange (mvcc.bucketMap log) (mvcc.revBytes ⟨minRev, 0⟩ false)
      (mvcc.revBytes ⟨maxRev, 0⟩ false) =
      (mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)).map mvcc.KvEnt.pair := by
    have := mvcc.bucketRange_logEnts log hwf hlen hcs _ _ hlo hhi
    rw [mvcc.W64_sint_nat _ Hrng.1, mvcc.W64_sint_nat _ h1] at this
    exact this
  iunfold mvcc.rangeVals at Hkv
  rw [hbr]
  wp_apply (hKvs lg g W ks vs (mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)) Rd Tok)
    $$ [$Hg $Hkv $Hrc $Htok] as %evs ⟨Hg, Htok, %ps, Hevs, Hcap, %Hps, Hdone⟩
  · ipureintro; exact mvcc.logEnts_bounds log hlen hcs _ _ hhi
  (try wp_auto)
  wp_apply HRU $$ [$Htok]
  (try wp_auto)
  have hev : mvcc.entsEvents W (mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)) =
      (mvcc.logEvents log (sint.nat minRev) (sint.nat maxRev)).filter
        (fun ev => mvcc.wgCovers W ev.kv.key) := by
    unfold mvcc.entsEvents; rw [mvcc.logEnts_events log hwf hlen hcs _ _ hhi]
  rw [hev] at Hps
  rw [hev]
  iapply HΦ
  iframe
  ipureintro; exact Hps

end proof

end EtcdGrove
end Perennial
