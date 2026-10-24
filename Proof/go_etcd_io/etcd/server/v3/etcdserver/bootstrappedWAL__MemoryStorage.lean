/-
Proof of `(*bootstrappedWAL).MemoryStorage()`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__MemoryStorage.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__MemoryStorage
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedWAL.MemoryStorage.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF))
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF))
    (wp_Append : MemoryStorage.Append.spec (GF := GF)) :
    bootstrappedWAL.MemoryStorage.spec (GF := GF) := by
  intro w dq dqs dqe bw sv hs es cap Hwf Hlen_bound Hcap_le
  wp_start as Hpre
  iNamed Hpre
  icases typedPointsto_not_null_dup _ _ _ $$ Hwal with ⟨Hwal, %Hwnn⟩
  iStructNamedSuffix Hwal "W"
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraftinit
  iunfold isInitialized at Hinit
  iNamed Hinit
  icases ErrSnapOOD with ⟨%eood, #Heood⟩
  ihave HstOpt : (|==> hsOpt (GF := GF) bw.st' hs) $$ [Hst]
  · icases Hst with (⟨%Hstn, %Hhs0⟩ | Hst)
    · imodintro; iunfold hsOpt; ileft; ipureintro; exact ⟨Hstn, Hhs0⟩
    · imod hsPts_persist bw.st' dqs hs $$ Hst with #HstRO
      imodintro; iunfold hsOpt; iright; iexact HstRO
  imod HstOpt with #HstOpt
  have Hcap0 : uint.Z (memStorEmpty : StorState).prev.index' ≤ cap := by
    have : 0 ≤ uint.Z sv.Metadata'.Index' := by word
    change 0 ≤ cap; omega
  (try wp_auto)
  wp_apply (wp_NewMemoryStorage cap Hcap0) $$ [$Hraftinit]
    as %ms %γs ⟨%Hcap, Hms, Hmeta, Htok, Hcert⟩
  (try wp_auto)
  -- Step 1: `if wal.snapshot != nil { s.ApplySnapshot(wal.snapshot) }`
  wp_join iprop(
      "s" ∷ s_ptr ↦ ms ∗
      "wal" ∷ wal_ptr ↦ w ∗
      "snapshotW" ∷ w.[bootstrappedWAL, go!"snapshot"] ↦{dq} bw.snapshot' ∗
      "Hms" ∷ ownMemoryStorage ms γs (memStorApplied sv) ∗
      "Htok" ∷ memSnapTok ms γs (memStorApplied sv))
    at next with [s wal snapshotW Hms Htok Hcert] as Hjoined1
  · wp_if_destruct
    · -- `bw.snapshot' = null`
      iunfold snapOptRO at Hsnap
      icases Hsnap with (⟨-, %Hsv0⟩ | #HsnapS)
      · (try wp_auto)
        have Hemp : memStorEmpty = memStorApplied sv := by
          rw [Hsv0]; rfl
        ihave Hms : ownMemoryStorage ms γs (memStorApplied sv) $$ [Hms]
        · rw [← Hemp]; iexact Hms
        ihave Htok : memSnapTok ms γs (memStorApplied sv) $$ [Htok]
        · rw [← Hemp]; iexact Htok
        isplitr; · itrivial
        simp only [named]; iframe
      · iunfold ownSnapS at HsnapS
        icases HsnapS with ⟨%ds, %pm, %uf, %Hnn, -⟩
        exact absurd Hif Hnn
    · -- `bw.snapshot' ≠ null`
      iunfold snapOptRO at Hsnap
      icases Hsnap with (⟨%Hfn, -⟩ | #HsnapS)
      · exact absurd Hfn Hif
      iunfold memCertAuth at Hcert
      imod monoListAuthOwn_update_app [(snapTrip sv sv.Metadata'.ConfState'.lists, false)] $$ Hcert
        with ⟨Hcert, #Hlb⟩
      ihave #Hscert := memStorCert_of_lb γs _
        (snapTrip sv sv.Metadata'.ConfState'.lists, false)
        (snapTrip sv sv.Metadata'.ConfState'.lists)
        (by simp) (by simp [certCovers]) $$ Hlb
      ihave HsnapArg : snapArg bw.snapshot' DFrac.discard sv $$ []
      · iunfold snapArg; iright; iexact HsnapS
      have Hidx_lt : uint.Z sv.Metadata'.Index' < 2 ^ 61 := by omega
      have Hfl_le : uint.Z memStorEmpty.fl ≤ uint.Z sv.Metadata'.Index' := by
        change 0 ≤ uint.Z sv.Metadata'.Index'; word
      have Hcap_le' : uint.Z sv.Metadata'.Index' ≤ γs.cap := by omega
      wp_apply wp_ApplySnapshot ms γs memStorEmpty memStorEmpty bw.snapshot' sv DFrac.discard eood
        rfl Hidx_lt Hfl_le Hcap_le'
        $$ [$Hraftinit $Hms $Htok $HsnapArg $Hscert $Heood]
        as %err ⟨-, (⟨%Hbad, -⟩ | ⟨-, Hms, Htok⟩)⟩
      · exact absurd rfl Hbad.1
      (try wp_auto)
      have Hfl_eq : ({ memStorApplied sv with fl := memStorEmpty.fl } : StorState) = memStorApplied sv := rfl
      ihave Hms : ownMemoryStorage ms γs (memStorApplied sv) $$ [Hms]
      · rw [← Hfl_eq]; iexact Hms
      isplitr; · itrivial
      simp only [named]; iframe
  iNamed Hjoined1
  (try wp_auto)
  -- Step 2: `if wal.st != nil { s.SetHardState(wal.st) }`
  wp_join iprop(
      "s" ∷ s_ptr ↦ ms ∗
      "wal" ∷ wal_ptr ↦ w ∗
      "stW" ∷ w.[bootstrappedWAL, go!"st"] ↦{dq} bw.st' ∗
      "Hmeta" ∷ memStorMeta ms γs hs)
    at next with [s wal stW Hmeta] as Hjoined2
  · wp_if_destruct
    · -- `bw.st' = null`
      iunfold hsOpt at HstOpt
      icases HstOpt with (⟨-, %Hhs0⟩ | #HstRO)
      · (try wp_auto)
        ihave Hmeta : memStorMeta ms γs hs $$ [Hmeta]
        · rw [Hhs0]; iexact Hmeta
        isplitr; · itrivial
        simp only [named]; iframe
      · iunfold hsRO at HstRO
        icases HstRO with ⟨%pt, %pv, %pc, %uf, %Hnn, -⟩
        exact absurd Hif Hnn
    · -- `bw.st' ≠ null`
      wp_apply wp_SetHardState ms γs hsZero bw.st' hs $$ [$Hraftinit $Hmeta $HstOpt] as Hmeta
      (try wp_auto)
      isplitr; · itrivial
      simp only [named]; iframe
  iNamed Hjoined2
  -- Step 3: `if len(wal.ents) != 0 { s.Append(wal.ents) }`
  iunfold entsPts at Hents
  icases Hents with ⟨%ls, Hs, #Hb⟩
  ihave %Heq := entsBig_length _ _ $$ Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave Hents : entsPts bw.ents' dqe es $$ [Hs]
  · iunfold entsPts; iexists ls; iframe Hs Hb
  (try wp_auto)
  wp_if_destruct
  · -- `bw.ents'.len = W64 0`
    have Hempty : es = [] := by
      apply List.eq_nil_of_length_eq_zero
      have : ls.length = 0 := by rw [Hlen.1, Hif]; rfl
      omega
    (try wp_auto)
    ihave Hwal : w ↦{dq} bw $$ [lgW haveWALW wW stW entsW snapshotW meta'W]
    · iapply typedPointsto_combine _ _ _ Hwnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iapply HΦ
    iexists γs
    isplitr; · ipureintro; exact Hcap
    have Hms_eq : ({ memStorApplied sv with ents := es } : StorState) = memStorApplied sv := by
      rw [Hempty]; rfl
    rw [Hms_eq]
    iframe Hms Hmeta Htok Hwal HstOpt Hents
  · -- `bw.ents'.len ≠ W64 0`
    have Hne : es ≠ [] := by
      intro hnil
      apply Hif
      have h0 : ls.length = 0 := by rw [Heq, hnil]; rfl
      have hlen1 := Hlen.1
      have hlen2 := Hlen.2
      rw [h0] at hlen1
      unfold sint.nat at hlen1
      unfold sint.Z at hlen2
      have : BitVec.toInt bw.ents'.len = 0 := by omega
      word
    obtain ⟨Hpok, Hpab, Habs⟩ := pendOk_memStorApplied_of_plogWf sv es Hne Hwf
    imod memStorage_handout ms γs (memStorApplied sv) es ⟨rfl, Hpok, Hpab⟩ $$ Hms with ⟨Hms, Haptok⟩
    have Hbnd_app : ∀ e0, es.head? = some e0 → uint.Z e0.Index' + (es.length : Int) ≤ 2 ^ 61 := by
      intro e0 he0
      rcases es with _ | ⟨e0', rest⟩
      · cases he0
      · cases he0
        have he0_idx : uint.Z e0.Index' = uint.Z sv.Metadata'.Index' + 1 := by
          have h0 := Hwf 0 e0 rfl
          simp only [snapId] at h0
          omega
        omega
    ihave Haptok' : (⌜es = []⌝ ∨ memAppendTok ms γs (memStorApplied sv) es) $$ [Haptok]
    · iright; iexact Haptok
    ihave Hs_hide : (True -∗ s_ptr ↦ ms) $$ [s]
    · iintro -; iexact s
    wp_apply wp_Append ms γs (memStorApplied sv) es bw.ents' dqe Hbnd_app
      $$ [$Hraftinit $Haptok' $Hents]
      as ⟨(%Hnil | Haptd), Hents⟩
    · exact absurd Hnil Hne
    imod memStorage_absorb ms γs { memStorApplied sv with pend := es } (memStorApplied sv) es
      $$ Hms Haptd with ⟨-, Hms⟩
    ihave Hms : ownMemoryStorage ms γs { memStorApplied sv with ents := es } $$ [Hms]
    · rw [← Habs]; iexact Hms
    ihave s : s_ptr ↦ ms $$ [Hs_hide]
    · iapply Hs_hide; itrivial
    (try wp_auto)
    ihave Hwal : w ↦{dq} bw $$ [lgW haveWALW wW stW entsW snapshotW meta'W]
    · iapply typedPointsto_combine _ _ _ Hwnn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iapply HΦ
    iexists γs
    isplitr; · ipureintro; exact Hcap
    iframe Hms Hmeta Htok Hwal HstOpt Hents

end proof

end EtcdGrove
end Perennial
