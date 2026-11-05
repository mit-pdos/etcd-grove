/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.rangeEvents
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchScan
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  intro lg b γ Wr P f q log minRev maxRev g W RT WT NC Wi Dep Cmp PutOk Rb Bt MW SR SRh qc c
  wp_start as ⟨#Hbk, Hrt, Hcu, Hview, #Hcert, Hg, %Hrng⟩
  ihave %Hwf : ⌜mvcc.LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝ $$ [Hcert]
  · iunfold mvcc.idxCert at Hcert
    icases Hcert with ⟨-, %H, -⟩
    ipureintro; exact H
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
  -- the view's bucket `m0`, thin of `log`'s (M2's item 15)
  iunfold mvcc.bucketViewL at Hview
  icases Hview with ⟨%m0, Hview, #Hbl⟩
  wp_apply HR $$ [$Hview $Hrt] as %rt ⟨Hview, Hsnap⟩
  icases Hsnap with ⟨%L, HL, #Hsnap⟩
  iunfold mvcc.keyReadSnap at Hsnap
  (try wp_auto)
  wp_bind (App (Val #(methods rt.ty go!"RLock" rt.v)) _)
  iapply Hsnap $$ %q [HL Hview]
  · iframe HL Hview
  inext
  iintro ⟨Hview, %m', %Rd, %Tok, Htok, #Hlk, #Hthin0⟩
  ihave #Hthin := mvcc.snapThin_trans (mvcc.bucketMap log) m0 m' (mvcc.delKey γ) $$ [Hthin0]
  · isplitl []
    · iapply mvcc.bucketLog_thin; iexact Hbl
    · iexact Hthin0
  -- the snapshot has every entry above the compaction revision, and every entry of the scanned
  -- revisions when revision `c` changes each key once (or no compaction)
  obtain ⟨hwf0, hlen0, hcs0⟩ := Hwf
  have hlo' : sint.nat minRev < 2 ^ 63 := by
    have : sint.Z minRev < 2 ^ 63 := by word
    show (sint.Z minRev).toNat < 2 ^ 63; omega
  have hz : ((sint.nat minRev : Nat) : Int) = sint.Z minRev := by
    show ((sint.Z minRev).toNat : Int) = sint.Z minRev; have := Hrng.1; omega
  icases mvcc.snapThin_scan_full γ qc c log m' (sint.nat minRev) hwf0 hlen0 hcs0 Hrng.2.2.2.1
      hlo' $$ [$Hcu $Hthin $Hcert] with ⟨Hcu, %Hagree⟩
  ihave #Hthin' := Hthin
  iunfold mvcc.snapThin at Hthin'
  icases Hthin' with ⟨%Hsub, -⟩
  ihave #Hrange := mvcc.keyReadLocked_range _ _ _ _ _ _ $$ Hlk
  iunfold mvcc.keyReadLocked at Hlk
  icases Hlk with ⟨#HRU, -, -, #Hrc⟩
  (try wp_auto)
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  iunfold mvcc.keyRangeReadSpec at Hrange
  ihave HRg := Hrange $$ %bK %mn' %mx'
  (try wp_auto)
  wp_apply HRg $$ [$HKeyG $Htok $Hmn $Hmx] as %ks %vs ⟨Htok, Hmn, Hmx, #Hkv⟩
  · ipureintro; simp [mvcc.revBytes]
  (try wp_auto)
  have hwf := hwf0
  have hlen := hlen0
  have hcs := hcs0
  have h1 : 0 ≤ sint.Z maxRev := Hrng.2.1
  have hlo : sint.nat minRev < 2 ^ 63 := by
    have : sint.Z minRev < 2 ^ 63 := by word
    show (sint.Z minRev).toNat < 2 ^ 63; omega
  have hhi : sint.nat maxRev ≤ log.length := by unfold sint.nat; unfold sint.Z at *; omega
  have hbr : mvcc.bucketRange (mvcc.bucketMap log) (mvcc.revBytes ⟨minRev, 0⟩ false)
      (mvcc.revBytes ⟨maxRev, 0⟩ false) =
      (mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)).map mvcc.KvEnt.pair := by
    have := mvcc.bucketRange_logEnts log hwf hlen hcs _ _ hlo hhi
    rw [mvcc.W64_sint_nat _ Hrng.1, mvcc.W64_sint_nat _ h1] at this
    exact this
  -- the snapshot's scan is the bucket's, filtered to the snapshot's entries (`P`)
  let P : mvcc.KvEnt → Bool := fun e => decide (m' !! e.pair.1 = some e.pair.2)
  have hbr' : mvcc.bucketRange m' (mvcc.revBytes ⟨minRev, 0⟩ false)
      (mvcc.revBytes ⟨maxRev, 0⟩ false) =
      ((mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)).filter P).map mvcc.KvEnt.pair := by
    rw [mvcc.bucketRange_sub (mvcc.bucketMap log) m' _ _ Hsub, hbr, List.filter_map]; rfl
  -- the scanned entries are the bucket's, from `minRev` on
  have hent : ∀ e ∈ mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev),
      mvcc.bucketMap log !! e.pair.1 = some e.pair.2 ∧
        go.GoStringLe (mvcc.revBytes ⟨minRev, 0⟩ false) e.pair.1 := by
    intro e he
    obtain ⟨-, hmem⟩ := (mvcc.bucketRange_eq_iff (mvcc.bucketMap log)
      (mvcc.revBytes ⟨minRev, 0⟩ false) (mvcc.revBytes ⟨maxRev, 0⟩ false) _).1 rfl
    have hm : (e.pair.1, e.pair.2) ∈ mvcc.bucketRange (mvcc.bucketMap log)
        (mvcc.revBytes ⟨minRev, 0⟩ false) (mvcc.revBytes ⟨maxRev, 0⟩ false) := by
      rw [hbr]; exact List.mem_map_of_mem he
    obtain ⟨h1, h2, -⟩ := (hmem _ _).1 hm
    exact ⟨h1, h2⟩
  have hP : (∀ e ∈ mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev), c < sint.Z e.rev.main →
        P e = true) ∧
      ((c = -1 ∨ mvcc.oneChangePerKeyAt log c) →
        ∀ e ∈ mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev), P e = true) := by
    refine ⟨fun e he hc => ?_, fun hnd e he => ?_⟩
    · obtain ⟨h1, -⟩ := hent e he
      exact decide_eq_true (Hagree.1 _ _ e.rev e.tomb h1 rfl hc)
    · obtain ⟨h1, h2⟩ := hent e he
      exact decide_eq_true (Hagree.2 hnd (by rw [hz]; exact Hrng.2.2.2.2) _ _ h1
        (by rw [mvcc.W64_sint_nat _ Hrng.1]; exact h2))
  iunfold mvcc.rangeVals at Hkv
  rw [hbr']
  wp_apply (hKvs lg g W ks vs ((mvcc.logEnts log (sint.nat minRev) (sint.nat maxRev)).filter P)
      Rd Tok)
    $$ [$Hg $Hkv $Hrc $Htok] as %evs ⟨Hg, Htok, %ps, Hevs, Hcap, %Hps, Hdone⟩
  · ipureintro
    exact fun e he => mvcc.logEnts_bounds log hlen hcs _ _ hhi e (List.mem_filter.1 he).1
  (try wp_auto)
  -- (by hand: `wp_apply` aborts here)
  wp_bind (App (Val #(methods rt.ty _ rt.v)) (Val #()))
  iapply HRU $$ [Htok]
  · iexact Htok
  inext
  iintro Hrt
  (try wp_auto)
  ihave Hview : mvcc.bucketViewL γ q log $$ [Hview]
  · iunfold mvcc.bucketViewL; iexists m0; iframe Hview; iexact Hbl
  iapply HΦ
  iframe
  ipureintro; exact ⟨hP, Hps⟩

end proof

end EtcdGrove
end Perennial
