/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__snapshot.lean`.
Lean-first (no Rocq counterpart; kvreconf's `Replica.snapshot` proof, with each storage change made
under `dmu` to the `MemoryStorage` and to the image, 2026-11-01, stage II (h)).

The request (`snapReqOk`) gives the `MemoryStorage`'s calls all they take, as in kvreconf: either
answer of `CreateSnapshot` raises what is known of the stored snapshot to the request's index
(`memSnapLb`); the compaction target `x = first + below(hi - first + 1)` is in `[first, hi]`, `hi` the
least of the request's bound and the known stored index, so its entry is frozen, the node applied it
and the stored snapshot reaches it. Under `dmu` the image changes with the `MemoryStorage`
(`Storage.CreateSnapshot`, `Storage.Compact`), and `dmu`'s record of it is kept (`create_ok`,
`compact_ok`, `kdPhaseInv_transport`): its shape, its snapshot's certificate (the request's), the
durable state each phase holds.

SPEC-GAP (2026-11-01, stage II (h), reported): what the image must satisfy for the two changes is not
derivable from `kdDmuInv`, `snapReqOk` and `memSnapLb`, which tie the image to the `MemoryStorage`
only through the hard state:
- `snap_create_gap`: the request's index `i` (unless the image already has a snapshot at `i` or
  later) is at most the image's commit index (a stored snapshot is at most the stored commit,
  `StorageHolds`), and the image's term at `i` is the frozen entry's that the request's certificate
  is about;
- `snap_known_gap`: the known stored index `known` (a lower bound of the `MemoryStorage`'s snapshot
  index) is at most the image's snapshot index (a compaction past the image's snapshot breaks
  `KdFileOk`/`StorageHolds`).
Both hold in the program (the image and the `MemoryStorage` change together under `dmu`; the image's
commit index is the driver's, which the applied index never passes; the stored snapshot's index is
monotone and `ErrSnapOutOfDate` answers alike), but the client can bound neither the
`MemoryStorage`'s snapshot index from above (its authority is the storage's lock's) nor its log above
the commit index (raft's, between `Ready`s: API gap G2), and holds no per-incarnation ghost name in
which `run` could record a lower bound of the image's commit, or the snapshotter one of the image's
snapshot, for `snapReqOk`/`memSnapLb` to cite.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__persist
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__CreateSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__Compact
public import Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ImageLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- `s.FirstIndex()` (the promoted `MemoryStorage.FirstIndex`). -/
theorem Storage.wp_FirstIndex (wp : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (c : Nat) :
  {{ kdStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memCompacted γs c) }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"FirstIndex")) (Val #()))
  {{ (fi : w64), RET (PairV #fi #interface.nil);
      ⌜c + 1 ≤ uint.nat fi⌝ ∗ memCompacted γs (uint.nat fi - 1) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs c $$ [HP] as %fi HQ
  · iexact HP
  iapply HΦ
  iexact HQ

/-- SPEC-GAP (see the file header): **a snapshot request's index against the image**: unless the
image has a snapshot at `i` or later, `i` is at most the image's commit index and the image's term
there is the request's frozen entry's. -/
private theorem snap_create_gap (γ : KdNames) (K : GName) (γs : MemStorNames) (M : StorFile)
    (i : w64) (e : EntryM) :
    memLog (GF := GF) γs (uint.nat i) DFrac.discard [e] ∗ (kdJ γ.r.cluster K).DL (uint.nat i) ⊢
      ⌜imgCreateStale M i ∨ (uint.nat i ≤ uint.nat M.hs.Commit' ∧ imgTermAt M i = e.Term')⌝ := by
  sorry

/-- SPEC-GAP (see the file header): **the known stored snapshot index against the image**: at most
the image's snapshot index. -/
private theorem snap_known_gap (γs : MemStorNames) (M : StorFile) (k : Nat) :
    memSnapLb (GF := GF) γs k ⊢ ⌜k ≤ uint.nat M.snap.Metadata'.Index'⌝ := by
  sorry

theorem Replica.snapshot.wp_proof
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_persist : Replica.persist.spec (GF := GF) (hG := hG))
    (wp_GetVotersOutgoing : raftpb.ConfState.GetVotersOutgoing.spec (GF := GF) (hG := hG))
    (wp_SCreate : Storage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_SCompact : Storage.Compact.spec (GF := GF) (hG := hG))
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG)) :
    Replica.snapshot.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ρ q known qp
  wp_start as ⟨#Hrr, Hreq, #Hkn, Hrun⟩
  iunfold snapReqOk at Hreq
  icases Hreq with ⟨Hsnap, Hcomp⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  ihave #HmsInv' := HmsInv
  iunfold memStorInvP at HmsInv'
  icases HmsInv' with ⟨#Hlock, -, -⟩
  try wp_auto
  iunfold errorsNewVar at ErrSnapOODNew
  icases ErrSnapOODNew with ⟨%xe, #Heood, -⟩
  ihave #Hc1 := isStats_field sts go!"SnapshotsTaken" (by decide) $$ Hstats
  ihave #Hc2 := isStats_field sts go!"SnapshotsTakenJoint" (by decide) $$ Hstats
  ihave #Hc3 := isStats_field sts go!"Compactions" (by decide) $$ Hstats
  -- the snapshot part: afterwards, `known` is a lower bound of the stored index
  wp_join iprop(∃ (k1 : w64) (ch : Bool), known_ptr ↦ k1 ∗ changed_ptr ↦ ch ∗ req_ptr ↦ q ∗
      r_ptr ↦ r ∗ memSnapLb ρ.γs (uint.nat k1))
    with [known changed req r Hsnap] as ⟨%k1, %ch1, known, changed, req, r, #Hkn1⟩
  · iexists known, false; iframe known changed req r; iexact Hkn
  · icases Hsnap with (%Hnil | ⟨%e, %cc, %bs, #He, #HSV, #HDL, #Hcert, #Hcs, Hdata⟩)
    · exfalso; exact Hif Hnil
    ihave %Hbs := ownSlice_len $$ Hdata
    ihave %Hcw := ownCSM_confWf $$ Hcs
    ihave #Hs0 : memSnapLb ρ.γs 0 $$ []
    · iapply (memSnapLb_mono ρ.γs (uint.nat known) 0 (Nat.zero_le _)); iexact Hkn
    -- the `MemoryStorage`'s call, as `Storage.CreateSnapshot` takes it
    have Hms : ∀ eood : GoInterface,
        {{ iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
            memStorInvP ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) ∗
            (kdJ γ.r.cluster ρ.key).SV (memSnapMade q.index' e.Term' cc bs) ∗
            (kdJ γ.r.cluster ρ.key).DL (uint.nat q.index') ∗
            memLog ρ.γs (uint.nat q.index') DFrac.discard [e] ∗ memSnapLb ρ.γs 0 ∗
            ownCSM q.cs' DFrac.discard cc ∗ globalAddr ErrSnapOutOfDate ↦□ eood) ∗
            q.data' ↦*{DFrac.own 1} bs }}
          (App (App (App (Val (ρ.ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
            (Val #q.index')) (Val #q.cs')) (Val #q.data'))
        {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
            memSnapLb (GF := GF) ρ.γs (uint.nat q.index') }} := by
      intro eood
      iintro %Φ ⟨⟨#Hr, #Hi, #Hsv, #Hdl, #Hlg, #Hz, #Hc, #Hg⟩, Hd⟩ HΦ
      iapply wp_CreateSnapshot ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) none q.index' e q.cs'
          DFrac.discard cc q.data' bs eood $$ [Hd]
      · rw [memStorAt_none]; iframe Hr Hi Hsv Hdl Hlg Hz Hc Hd Hg
      inext
      iintro %snap %err ⟨-, #Hlb, -⟩
      iapply HΦ; iexact Hlb
    try wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HI⟩
    iunfold kdDmuInv at HI
    iNamed HI
    icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert0, Hph⟩
    ihave %Hgap := snap_create_gap γ ρ.key ρ.γs M q.index' e $$ [He HDL]
    · iframe He HDL
    have Hpre : imgCreateStale M q.index' ∨ (uint.nat M.prev ≤ uint.nat q.index' ∧
        uint.nat q.index' ≤ uint.nat M.prev + M.ents.length) := by
      by_cases Hst : imgCreateStale M q.index'
      · left; exact Hst
      · right
        have h1 := (Hgap.resolve_left Hst).1
        obtain ⟨-, -, -, -, Hps, -, -, Hcl⟩ := HMok
        unfold imgCreateStale at Hst
        constructor <;> word
    try wp_auto
    wp_apply wp_SCreate st ρ.ms ρ.γs ip M q.index' q.cs' (some cc) q.data' (DFrac.own 1) bs _ _ _
        Hpre (Hms _) $$ [$Hpkg $Hrec $Himg $Himage $Hcs $Hdata $Heood $Hraft $HmsInv $HSV $HDL $He $Hs0]
      as %err ⟨⟨%snap0, %e0, #Hlb⟩, Hres⟩
    -- `dmu`'s record of the image kept; the error the image's
    ihave ⟨%Herr, HI⟩ : iprop(⌜err = interface.nil ∨ err = interface.mkOk (go.GoType.PointerType
        _root_.Perennial.errors.errorString.ty) #xe⌝ ∗ ▷ kdDmuInv γ id r n st ρ.ms ρ.γs ρ.ph) $$ [Hres Hcr Hmeta Hwr Hph]
    · by_cases Hst : imgCreateStale M q.index'
      · simp only [Hst, ↓reduceIte]
        icases Hres with ⟨%Herr, Himage⟩
        isplitr
        · ipureintro; right; exact Herr
        inext
        iunfold kdDmuInv
        iexists crashed, ip, M
        iframe Hcr Himg Himage Hmeta
        iexists S, o, pz
        iframe Hwr Hcert0 Hph
        ipureintro; exact HMok
      · simp only [Hst, ↓reduceIte]
        icases Hres with ⟨%Herr, Himage⟩
        obtain ⟨Hci, Hti⟩ := Hgap.resolve_left Hst
        have Hok' := create_ok M q.index' (some cc) bs HMok Hst Hci Hcw (by word)
        isplitr
        · ipureintro; left; exact Herr
        inext
        iunfold kdDmuInv
        iexists crashed, ip, imgCreateSnapshot M q.index' (some cc) bs
        rw [show (imgCreateSnapshot M q.index' (some cc) bs).hs = M.hs from rfl]
        iframe Hcr Himg Himage Hmeta
        iexists S, o, pz
        iframe Hwr
        isplitr
        · ipureintro; exact Hok'.1
        isplitr
        · simp only [imgCreateSnapshot, Option.getD_some, Hti]; iexact Hcert
        iapply kdPhaseInv_transport γ id n ρ.ph S M _ pz Hok'.2 $$ Hph
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked $HI]
    try wp_auto
    rcases Herr with rfl | rfl
    · -- taken
      try wp_auto
      wp_apply wp_add sts _ $$ [$Hpkg $Hc1]
      try wp_auto
      ihave #HcsO : csOpt q.cs' DFrac.discard cc $$ []
      · unfold csOpt; iright; iexact Hcs
      wp_apply wp_GetVotersOutgoing q.cs' DFrac.discard cc $$ [$Hpb $HcsO] as %vo ⟨-, -⟩
      try wp_auto
      try wp_if_destruct
      all_goals
        try wp_apply wp_add sts _ $$ [$Hpkg $Hc2]
        try wp_auto
        wp_if_destruct
        · wp_join_done; iexists q.index', true; iframe; iexact Hlb
        · wp_join_done; iexists known, true; iframe; iexact Hkn
    · -- out of date
      try wp_auto
      wp_if_destruct
      · wp_join_done; iexists q.index', false; iframe; iexact Hlb
      · wp_join_done; iexists known, false; iframe; iexact Hkn
  -- the compaction part
  wp_join iprop(∃ ch2 : Bool, changed_ptr ↦ ch2 ∗ known_ptr ↦ k1 ∗ req_ptr ↦ q ∗ r_ptr ↦ r)
    with [changed known req r Hcomp] as ⟨%ch2, changed, known, req, r⟩
  · icases Hcomp with (%H0 | ⟨%cp, %D, #Hcp, #Hfz0, %HD, #Hal⟩)
    · exfalso; simp_all
    ihave #Hfz : kvreconf.frozenTo ρ.γs cp D $$ []
    · unfold kvreconf.frozenTo; iexact Hfz0
    wp_apply Storage.wp_FirstIndex wp_FirstIndex st ρ.ms ρ.γs cp $$ [$Hrec $Hraft $Hlock $Hcp]
      as %fi ⟨%Hfi, -⟩
    try wp_auto
    wp_if_destruct
    all_goals
      try wp_auto
      wp_if_destruct
      rotate_left
      · first | (iexists ch1; iframe) | (wp_join_done; iexists ch1; iframe) | wp_join_done
      wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HI⟩
      try wp_auto
      wp_apply wp_below $$ [$Hpkg] as %rb %Hrb
      try wp_auto
      icases kvreconf.frozenTo_at ρ.γs cp D (uint.nat (fi + rb)) (by word) (by word) $$ Hfz
        with ⟨%ex, #Hex, -⟩
      ihave %Hx61 := memLog_bound $$ Hex
      iunfold kdDmuInv at HI
      iNamed HI
      icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert0, Hph⟩
      ihave %Hkg := snap_known_gap ρ.γs M (uint.nat k1) $$ Hkn1
      ihave ⟨%HhS, Hph⟩ := kdPhaseInv_holds γ id n ρ.ph S M pz $$ Hph
      obtain ⟨S0, HhS⟩ := HhS
      have Hxs : uint.nat (fi + rb) ≤ uint.nat M.snap.Metadata'.Index' := by word
      have Hs0 : M.snap.Metadata'.Index' ≠ W64 0 := by intro h; rw [h] at Hxs; word
      have Hsc := holds_snap_commit S0 M HhS Hs0
      have Hxl : uint.nat (fi + rb) ≤ uint.nat M.prev + M.ents.length := by
        obtain ⟨-, -, -, -, -, Hsl, -, -⟩ := HMok; omega
      -- the `MemoryStorage`'s call, as `Storage.Compact` takes it
      have Hmc : ∀ eco : GoInterface,
          {{ iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
              memStorInvP ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) ∗
              (kdJ γ.r.cluster ρ.key).B (uint.nat (fi + rb)) ∗
              memLog ρ.γs (uint.nat (fi + rb)) DFrac.discard [ex] ∗
              memSnapLb ρ.γs (uint.nat (fi + rb)) ∗ globalAddr ErrCompacted ↦□ eco) }}
            (App (Val (ρ.ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact"))
              (Val #(fi + rb)))
          {{ (e : GoInterface), RET #e; True }} := by
        intro eco
        iintro %Φ ⟨#Hr, #Hi, #HB, #Hlg, #Hlb, #Hg⟩ HΦ
        iapply wp_Compact ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) none (fi + rb) eco $$ []
        · rw [memStorAt_none]; iframe Hr Hi HB Hlb Hg
          ileft; iexists ex; iexact Hlg
        inext
        iintro %err -
        iapply HΦ; itrivial
      ihave #HB : (kdJ γ.r.cluster ρ.key).B (uint.nat (fi + rb)) $$ []
      · unfold kdJ
        iapply nodeAppliedLb_mono γ.r.cluster ρ.key (uint.nat q.compact') _ (by word) $$ Hal
      ihave #Hxlb : memSnapLb ρ.γs (uint.nat (fi + rb)) $$ []
      · iapply (memSnapLb_mono ρ.γs (uint.nat k1) (uint.nat (fi + rb)) (by word))
        iexact Hkn1
      try wp_auto
      wp_apply wp_SCompact st ρ.ms ρ.γs ip M (fi + rb) errCompacted _ _ Hxl (Hmc _)
          $$ [$Hpkg $Hrec $Himg $Himage $ErrCompacted $Hraft $HmsInv $HB $Hex $Hxlb]
        as %err ⟨-, Hres⟩
      ihave ⟨%Herr, HI⟩ : iprop(⌜err = interface.nil ∨ err = errCompacted⌝ ∗
          ▷ kdDmuInv γ id r n st ρ.ms ρ.γs ρ.ph) $$ [Hres Hcr Hmeta Hwr Hph]
      · by_cases Hst : imgCompactStale M (fi + rb)
        · simp only [Hst, ↓reduceIte]
          icases Hres with ⟨%Herr, Himage⟩
          isplitr
          · ipureintro; right; exact Herr
          inext
          iunfold kdDmuInv
          iexists crashed, ip, M
          iframe Hcr Himg Himage Hmeta
          iexists S, o, pz
          iframe Hwr Hcert0 Hph
          ipureintro; exact HMok
        · simp only [Hst, ↓reduceIte]
          icases Hres with ⟨%Herr, Himage⟩
          have Hok' := compact_ok M (fi + rb) HMok Hst Hxs (by
            rcases Hx61 with h | h
            · cases h
            · simp only [List.length_singleton] at h; word) (by omega)
          isplitr
          · ipureintro; left; exact Herr
          inext
          iunfold kdDmuInv
          iexists crashed, ip, imgCompact M (fi + rb)
          rw [show (imgCompact M (fi + rb)).hs = M.hs from rfl,
            show (imgCompact M (fi + rb)).snap = M.snap from rfl]
          iframe Hcr Himg Himage Hmeta
          iexists S, o, pz
          iframe Hwr Hcert0
          isplitr
          · ipureintro; exact Hok'.1
          iapply kdPhaseInv_transport γ id n ρ.ph S M _ pz Hok'.2 $$ Hph
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked $HI]
      try wp_auto
      rcases Herr with rfl | rfl
      · try wp_auto
        wp_apply wp_add sts _ $$ [$Hpkg $Hc3]
        try wp_auto
        wp_join_done
      · obtain ⟨ie, Hie⟩ : ∃ ie, err = GoInterface.ok ie := by
          cases h : err with
          | nil => exact absurd h HErrCompacted
          | ok ie => exact ⟨ie, rfl⟩
        subst Hie
        try wp_auto
        wp_join_done
  -- a write one time in two, if the storage changed
  cases ch2
  · try wp_auto
    iapply HΦ
    iframe Hrun Hkn1
  · try wp_auto
    wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b -
    cases b
    · try wp_auto
      iapply HΦ
      iframe Hrun Hkn1
    · try wp_auto
      wp_apply wp_persist γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph qp $$ [$Hrep $Hrun] as %ok Hrun
      try wp_auto
      iapply HΦ
      iframe Hrun Hkn1

end proof

end kvdurable
end EtcdGrove
end Perennial
