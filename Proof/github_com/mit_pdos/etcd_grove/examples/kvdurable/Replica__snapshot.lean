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

What the image must satisfy for the two changes (2026-11-01, stage II (h)) comes from `dmu`'s record
of it and the lower bounds the request and the snapshotter cite: the request's index is at most the
image's frozen bound (`ρ.ph.ic`), which is at most its commit index unless at its log's start, and
the image's entries up to it are the `MemoryStorage`'s frozen ones (`frozen_term`); `known` is at
most the image's snapshot index (`ρ.ph.is`), which either answer of `CreateSnapshot` raises to the
request's index. A compaction keeps the frozen record (`frozen_compact`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.KdStorageApi
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
  wp_start as ⟨#Hrr, Hreq, #Hkn, #Hkni, Hrun⟩
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
      r_ptr ↦ r ∗ memSnapLb ρ.γs (uint.nat k1) ∗ monoNatLbOwn ρ.ph.is (uint.nat k1))
    with [known changed req r Hsnap] as ⟨%k1, %ch1, known, changed, req, r, #Hkn1, #Hkni1⟩
  · iexists known, false; iframe known changed req r; iframe Hkn Hkni
  · icases Hsnap with (%Hnil | ⟨%e, %cc, %bs, #He, #Hicl, #HSV, #HDL, #Hcert, #Hcs, Hdata⟩)
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
    icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert0, %Hfb, Hph⟩
    ihave %Hifz := monoNatLbOwn_valid ρ.ph.ic 1 fz (uint.nat q.index') $$ Hic Hicl
    ihave %Hgap : ⌜imgCreateStale M q.index' ∨
        (uint.nat q.index' ≤ uint.nat M.hs.Commit' ∧ imgTermAt M q.index' = e.Term')⌝ $$ []
    · by_cases Hst : imgCreateStale M q.index'
      · ipureintro; left; exact Hst
      · have Hns := Hst
        unfold imgCreateStale at Hns
        obtain ⟨-, -, -, -, Hps, -, -, Hcl⟩ := HMok
        have Hpi : uint.nat M.prev < uint.nat q.index' := by word
        have Hci : uint.nat q.index' ≤ uint.nat M.hs.Commit' := by
          rcases Hfzc with h | h <;> omega
        ihave %Ht := frozen_term ρ.γs M fz q.index' e Hpi Hifz.2 (by omega) $$ [$Hfz $He]
        ipureintro; right; exact ⟨Hci, Ht⟩
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
    ihave Hblk : iprop(|==> (⌜err = interface.nil ∨ err = interface.mkOk (go.GoType.PointerType
        _root_.Perennial.errors.errorString.ty) #xe⌝ ∗ ▷ kdDmuInv γ id r n st ρ.ms ρ.γs ρ.ph ∗
        monoNatLbOwn ρ.ph.is (uint.nat q.index'))) $$ [Hres Hcr Hmeta Hwr Hph Hic His Hcm]
    · by_cases Hst : imgCreateStale M q.index'
      · imodintro
        simp only [Hst, ↓reduceIte]
        icases Hres with ⟨%Herr, Himage⟩
        ihave #Hsl := monoNatLbOwn_get ρ.ph.is 1 _ $$ His
        isplitr
        · ipureintro; right; exact Herr
        isplitl
        · inext
          iunfold kdDmuInv
          iexists crashed, ip, M, fz
          iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm
          isplitr
          · ipureintro; exact Hfzc
          iexists S, o, pz
          iframe Hwr Hcert0 Hph
          ipureintro; exact ⟨HMok, Hfb⟩
        unfold imgCreateStale at Hst
        iapply monoNatLbOwn_le (uint.nat q.index') (by word) $$ Hsl
      · simp only [Hst, ↓reduceIte]
        icases Hres with ⟨%Herr, Himage⟩
        have Hns := Hst
        unfold imgCreateStale at Hns
        imod mono_nat_own_update (uint.nat q.index') (by word) $$ His with ⟨His, #Hsl⟩
        imodintro
        obtain ⟨Hci, Hti⟩ := Hgap.resolve_left Hst
        have Hok' := create_ok M q.index' (some cc) bs HMok Hst Hci Hcw (by word)
        isplitr
        · ipureintro; left; exact Herr
        iframe Hsl
        inext
        iunfold kdDmuInv
        iexists crashed, ip, imgCreateSnapshot M q.index' (some cc) bs, fz
        rw [show (imgCreateSnapshot M q.index' (some cc) bs).hs = M.hs from rfl,
          show (imgCreateSnapshot M q.index' (some cc) bs).prev = M.prev from rfl,
          show (imgCreateSnapshot M q.index' (some cc) bs).ents = M.ents from rfl,
          show (imgCreateSnapshot M q.index' (some cc) bs).snap.Metadata'.Index' = q.index' from rfl]
        iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm
        isplitr
        · ipureintro; exact Hfzc
        iexists S, o, pz
        iframe Hwr
        isplitr
        · ipureintro; exact Hok'.1
        isplitr
        · simp only [imgCreateSnapshot, Option.getD_some, Hti]; iexact Hcert
        isplitr
        · ipureintro; exact Hfb
        iapply kdPhaseInv_transport γ id n ρ.ph.ph S M _ pz Hok'.2 $$ Hph
    imod Hblk with ⟨%Herr, HI, #Hilb⟩
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
        · wp_join_done; iexists q.index', true; iframe; iframe Hlb Hilb
        · wp_join_done; iexists known, true; iframe; iframe Hkn Hkni
    · -- out of date
      try wp_auto
      wp_if_destruct
      · wp_join_done; iexists q.index', false; iframe; iframe Hlb Hilb
      · wp_join_done; iexists known, false; iframe; iframe Hkn Hkni
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
      icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert0, %Hfb, Hph⟩
      ihave %Hkg := monoNatLbOwn_valid ρ.ph.is 1 _ (uint.nat k1) $$ His Hkni1
      ihave ⟨%HhS, Hph⟩ := kdPhaseInv_holds γ id n ρ.ph.ph S M pz $$ Hph
      obtain ⟨S0, HhS⟩ := HhS
      have Hxs : uint.nat (fi + rb) ≤ uint.nat M.snap.Metadata'.Index' := by have := Hkg.2; word
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
          ▷ kdDmuInv γ id r n st ρ.ms ρ.γs ρ.ph) $$ [Hres Hcr Hmeta Hwr Hph Hic His Hcm]
      · by_cases Hst : imgCompactStale M (fi + rb)
        · simp only [Hst, ↓reduceIte]
          icases Hres with ⟨%Herr, Himage⟩
          isplitr
          · ipureintro; right; exact Herr
          inext
          iunfold kdDmuInv
          iexists crashed, ip, M, fz
          iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm
          isplitr
          · ipureintro; exact Hfzc
          iexists S, o, pz
          iframe Hwr Hcert0 Hph
          ipureintro; exact ⟨HMok, Hfb⟩
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
          have Hns := Hst
          unfold imgCompactStale at Hns
          ihave #Hfz' := frozen_compact ρ.γs M fz (fi + rb) (by word) Hxl $$ Hfz
          iexists crashed, ip, imgCompact M (fi + rb), fz
          rw [show (imgCompact M (fi + rb)).hs = M.hs from rfl,
            show (imgCompact M (fi + rb)).snap = M.snap from rfl,
            show (imgCompact M (fi + rb)).prev = fi + rb from rfl,
            show (imgCompact M (fi + rb)).ents = M.ents.drop (uint.nat (fi + rb) - uint.nat M.prev) from rfl]
          iframe Hcr Himg Himage Hmeta Hic Hfz' His Hcm
          isplitr
          · ipureintro; rcases Hfzc with h | h
            · left; exact h
            · right; word
          iexists S, o, pz
          iframe Hwr Hcert0
          isplitr
          · ipureintro; exact Hok'.1
          isplitr
          · ipureintro; exact Hfb
          iapply kdPhaseInv_transport γ id n ρ.ph.ph S M _ pz Hok'.2 $$ Hph
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
    iframe Hrun Hkn1 Hkni1
  · try wp_auto
    wp_apply wp_oneIn (W64 2) (by decide) $$ [$Hpkg] as %b -
    cases b
    · try wp_auto
      iapply HΦ
      iframe Hrun Hkn1 Hkni1
    · try wp_auto
      wp_apply wp_persist γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph qp $$ [$Hrep $Hrun] as %ok Hrun
      try wp_auto
      iapply HΦ
      iframe Hrun Hkn1 Hkni1

end proof

end kvdurable
end EtcdGrove
end Perennial
