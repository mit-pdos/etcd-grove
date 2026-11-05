/-
Proof of the spec of the same name: `WatchStream.Close.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).

The update fires when the stream's lock is taken, with the channel's invariant open
(`Api/StreamHandle.close_fire`): the client's state, open by the update's premise, is the stream's,
so the stream is open (a second `Close`, which would close the channel twice, is excluded by the
update, not by a token); the close is appended to the stream's history. Then every watcher is
cancelled, the stream marked closed and its channel closed, as before.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Close
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamHandle

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

theorem mvcc.watchStream.Close.wp_proof : mvcc.watchStream.Close.spec (GF := GF) (hG := hG) := by
  intro w γ ι Q
  wp_start as ⟨Hws, Htt, Hau⟩
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %γp, %hι, #Hinv, #Hws, -, -, -⟩
  obtain ⟨hι, hγ⟩ := hι
  generalize hch : (ι : api.WsAbs).ch = ch at hι
  have hι' : ι = (mvcc.wsAbsOf γw ch γc : api.WsAbs) := hι
  subst hι'
  have hγ' : γ = (γw.st : api.MvccName) := hγ.symm
  subst hγ'
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%g, #Hg, #HgS⟩, -⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  icases Hacl with ⟨%lm, %CS, Hm, Hcsl, %Hrel⟩
  wp_auto_lc 1
  -- the update, the stream open
  iapply fupd_wp
  iinv Hinv with Hi Hclose'
  imod lc_fupd_elim_later (E := ⊤ \ ↑mvcc.watchN) $$ Hlc1 Hi with Hi
  imod mvcc.api.close_fire γw ch γc Q nextID closed CM CS lm Hrel $$ [$Hi $Hm $Hau]
    with ⟨Hi, %lm', %S, Hm, HQ, %Hcl'⟩
  obtain ⟨hcl, hrel'⟩ := Hcl'
  imod Hclose' $$ [Hi] with -
  · inext; iexact Hi
  imodintro
  subst hcl
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hcl with ⟨%L, HCR, #HL, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ f : GoFunc,
      "cancel" ∷ cancel_ptr ↦ f ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "#Hdone" ∷ □ (∀ (id : w64) (w : Loc), ⌜id ∈ keys.take i.toNat⌝ -∗ ⌜WM !! id = some w⌝ -∗
        (mvcc.storeWatchParams s st γw).WC w))) $$ Hcm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [cancel]
  · iexists _
    simp only [named]
    iframe cancel
    isplitr
    · ipureintro; exact Int.le_refl _
    imodintro
    iintro %id %w %hin %_
    simp at hin
  isplitr
  · imodintro
    iintro %i %key %c ⟨%Hkey, %Hc⟩ HP
    iNamed HP
    obtain ⟨w, hw⟩ : ∃ w, WM !! key = some w := by
      have h := Hdom key
      rw [Hc] at h
      exact Option.isSome_iff_exists.1 (by simpa using h.symm)
    ihave #Hcspec := Hcs $$ %key %c %w %Hc %hw
    iunfold mvcc.cancelSpec at Hcspec
    wp_auto
    wp_apply Hcspec as #Hwc
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _
    simp only [named]
    iframe cancel
    isplitr
    · ipureintro; omega
    imodintro
    iintro %id %w' %hin %hw'
    have htake : (i + 1).toNat = i.toNat + 1 := by omega
    rw [htake, List.take_add_one, Hkey] at hin
    simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hin
    rcases hin with hin | rfl
    · iapply Hdone $$ %id %w' %hin %hw'
    · rw [hw] at hw'
      cases hw'
      simp only [mvcc.storeWatchParams]
      iexact Hwc
  iintro HP Hcm
  iNamed HP
  wp_auto
  have htk : List.take (↑CM.size : Int).toNat keys = keys := by
    rw [List.take_of_length_le]; omega
  rw [htk] at *
  wp_apply Hclose $$ [$HCR]
  · imodintro
    iintro %w %hin
    icases HL $$ %w %hin with (⟨%id, %hid⟩ | #Hcf)
    · have hk : id ∈ keys := by
        rw [Hkset, Hdom id, hid]; rfl
      iapply Hdone $$ %id %w %hk %hid
    · iunfold mvcc.cancelledFor at Hcf
      icases Hcf with ⟨#Hwc, -⟩
      iexact Hwc
  iunfold gaugeSpec at HgS
  icases HgS with ⟨-, #HDec, -⟩
  wp_apply HDec
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hm Hcsl]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, true, cm, wm, CM, WM
    simp only [named, ↓reduceIte]
    iframe HnextID Hclosed Hcf Hwf Hcm Hwm Hids
    iframe #
    isplitr
    · ipureintro; exact Hdom
    isplitr
    · ipureintro; exact Hnn
    isplitl [Hm Hcsl]
    · iexists lm', CS
      iframe Hm Hcsl
      ipureintro; exact hrel'
    iintro !> %id %w %hid
    have hk : id ∈ keys := by
      rw [Hkset, Hdom id, hid]; rfl
    iapply Hdone $$ %id %w %hk %hid
  iapply HΦ
  iframe Htt
  iexists S
  iexact HQ

end proof

end EtcdGrove
end Perennial
