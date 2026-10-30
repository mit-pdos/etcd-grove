/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__compactRaftLog.lean`. Lean-first
(no Rocq counterpart); the trust boundary (names-only) until 2026-10-26.

The body (`server.go`): `s.inflightSnapshots.Load()` (its invariant, `srvInflight`), returning
after an `Info` if it is not `0`; `compacti` from `SnapshotCatchUpEntries`;
`s.r.raftStorage.Compact(compacti)` (`MemoryStorage.Compact`'s premises: `compacti ≤ snapi`, at
most the floor and the snapshot, within the cap). `Compact` returns `nil` or raft's
`ErrCompacted`; of the latter `errors.Is(err, raft.ErrCompacted)` is `true` (an `errors.New`
error, `ErrCompactedNew`: a leaf pointer error, `ErrorStringLeaf`), so the `Panic` is dead.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__compactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Uint64
public import Perennial.Spec.sync.atomic.Int64__Load

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.compactRaftLog.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hCompact : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    EtcdServer.compactRaftLog.spec (GF := GF) (hG := hG) := by
  sorry
/- REPAIR-OLD
  -- (D22 J4) `Compact` over the shared token (`Compact.wp_shared`)
  have hCompact := MemoryStorage.Compact.wp_shared hCompact srvStorTokN srvStorTokN_disj
  intro s snapi ms γs γss sl scu l Hsl Hpos Hcap
  wp_start as ⟨Hlr, #Hlgf, %Hlgn, #Hinf, #Hrs, #Hro, #Htinv, #Hslb, #Hfl, #Hscu⟩
  ihave #Patm : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Praft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hLg s l $$ [$Hlr] as ⟨-, Hlr⟩
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)
  -- `s.inflightSnapshots.Load()`
  wp_apply_core sync.atomic.Int64.wp_Load (srvInflightAddr s) (DFrac.own 1) $$ [] [-]
  · iexact Patm
  ihave #Hinf' := Hinf
  iunfold srvInflight at Hinf'
  iinv Hinf' with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, Hv⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  (try wp_auto)
  by_cases hv : v0 = W64 0
  · -- nothing in flight: compact
    subst hv
    (try wp_auto)
    iunfold memFloorAtLeast at Hfl
    icases Hfl with ⟨%x, #Hft, %Hx⟩
    ihave #Hrinit := go_etcd_io.raft.v3.isInitialized_access $$ Praft
    unfold go_etcd_io.raft.v3.isInitialized
    icases Hrinit with ⟨%e1, %e2, %e3, %e4, %e5, %_, %_, %_, %_, %_, #Hrinit⟩
    iNamed Hrinit
    iunfold EtcdGrove.errorsNewVar at ErrCompactedNew
    icases ErrCompactedNew with ⟨%xc, #Hxc, -⟩
    icombine ErrCompacted Hxc gives %Heq
    subst Heq
    -- the compaction index, at most `snapi`
    have Hci : ∀ ci : w64, uint.Z ci =
        (if uint.Z scu < uint.Z snapi then uint.Z snapi - uint.Z scu else 1) →
        uint.Z ci ≤ uint.Z x ∧ uint.Z ci ≤ (uint.nat sl : Int) ∧ uint.Z ci ≤ γs.cap := by
      intro ci h
      have h0 : 0 ≤ uint.Z scu := by word
      have hle : uint.Z ci ≤ uint.Z snapi := by split at h <;> omega
      have := uint_nat_eq sl
      exact ⟨by omega, by omega, by rw [h]; exact Hcap⟩
    wp_if_destruct
    all_goals (
      (try wp_auto)
      first
        | (have H := Hci (snapi - scu) (by rw [if_pos (by word)]; word)
           wp_apply hCompact ms γs γss x (snapi - scu) (uint.nat sl) _ H.1 H.2.1 H.2.2 $$ []
             as %err %Hor
           · iframe #)
        | (have H := Hci (W64 1) (by rw [if_neg (by word)]; word)
           wp_apply hCompact ms γs γss x (W64 1) (uint.nat sl) _ H.1 H.2.1 H.2.2 $$ []
             as %err %Hor
           · iframe #)
      rcases Hor with Herr | Herr
      · -- `ErrCompacted`: `errors.Is` is `true`, return
        subst Herr
        (try wp_auto)
        obtain ⟨Hptr, Hleaf, HnoIs⟩ := errorString_leaf xc
        wp_apply hIs (· = interface.mkOk
            (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xc) (fun _ => False)
            _ _ (fun tii h => by cases h; exact Hptr)
            (_root_.Perennial.errors.treeTyped_pointer _ _ Hptr) $$ []
          as %b ⟨-, %Hb, -⟩
        · iframe #
          isplitl
          · iapply _root_.Perennial.errors.errorIsTree_leaf _ (fun _ => False) _ Hleaf HnoIs
          ipureintro; rfl
        rw [Hb _ rfl Hptr rfl]
        (try wp_auto)
        iapply HΦ
        iframe Hlr
      · -- compacted to `compacti`: log it
        subst Herr
        (try wp_auto)
        wp_apply hU64 $$ [] as %f -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply hDebug l $$ []
        · iframe #; ipureintro; exact Hlgn
        (try wp_auto)
        iapply HΦ
        iframe Hlr)
  · -- a snapshot in flight: skip
    rw [decide_eq_false hv]
    (try wp_auto)
    wp_apply hInfo l $$ []
    · iframe #; ipureintro; exact Hlgn
    (try wp_auto)
    iapply HΦ
    iframe Hlr
-/

end proof

end EtcdGrove
end Perennial
