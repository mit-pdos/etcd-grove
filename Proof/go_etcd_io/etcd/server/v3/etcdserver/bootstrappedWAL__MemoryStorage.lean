/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__MemoryStorage.lean`
(etcd-io/etcd#19693; pr-verify, 2026-10-17). Lean-first (no Rocq counterpart). Its callees are
raft's `MemoryStorage` (`NewMemoryStorage`, `ApplySnapshot`, `SetHardState`, `Append`: proved and
linked in raft's `Link.lean`); the append token is the storage owner's hand-out
(`memStorage_handout`), its receipt absorbed back (`memStorage_absorb`).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
-- (`memStorage_handout`/`memStorage_absorb` are stated in a section over raft's `StorageModel`)
variable [StorageModel GF]

set_option maxHeartbeats 0 in
theorem bootstrappedWAL.MemoryStorage.wp_proof
    (wp_New : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_Apply : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_SetHS : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG)) :
    bootstrappedWAL.MemoryStorage.spec (GF := GF) (hG := hG) := by
  intro w dqw v cs hs p dq eood Hhead Hlast Hpos
  wp_start as Hpre
  iNamed Hpre
  icases typedPointsto_not_null_dup _ _ _ $$ Hw with ⟨Hw, %Hwnn⟩
  iStructNamedSuffix Hw "W"
  icases typedPointsto_not_null_dup _ _ _ $$ posW with ⟨posW, %Hpnn⟩
  iStructNamedSuffix posW "P"
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_New $$ [] as %ms %γs ⟨Hms, Hmeta⟩
  (try wp_auto)
  -- `if wal.confstate != nil { s.ApplySnapshot(...) }`: either way the storage is `bwalBase`
  by_cases Hcp : v.confstate' = null
  case' pos =>
    rw [decide_eq_true Hcp]
    simp only [Bool.not_true]
    (try wp_auto)
    iclear Hcs
    rw [show memStorEmpty = bwalBase v.pos' v.confstate' cs by simp [bwalBase, Hcp]]
  case' neg =>
    rw [decide_eq_false Hcp]
    simp only [Bool.not_false]
    icases Hcs with (%Hc | Hcs)
    · exact absurd Hc Hcp
    (try wp_auto)
    rename_i pidx
    irename : (pidx ↦ v.pos'.Index' : IProp GF) => HcI
    imod cellRO_alloc _ _ $$ HcI with #HcI
    imod cellRO_alloc _ _ $$ «$v1» with #HcT
    imod smPts_of_struct «$v0_ptr»
      ({ state' := zeroValDef, ConfState' := v.confstate', Index' := pidx, Term' := «$v1_ptr»,
         unknownFields' := slice.nil, sizeCache' := 0 } : raftpb.SnapshotMetadata) (bwalSnap v.pos' cs).Metadata' ⊤ rfl $$ [«$v0» Hcs] with Hmd
    · simp only [bwalSnap]
      iframe «$v0» HcI HcT
      iunfold csOpt; iright; iexact Hcs
    ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSnapM_of_struct «$a0_ptr»
      ({ state' := zeroValDef, Data' := slice.nil, Metadata' := «$v0_ptr», unknownFields' := slice.nil,
         sizeCache' := 0 } : raftpb.Snapshot) (bwalSnap v.pos' cs) ⊤ rfl $$ [«$a0» Hnil Hmd] with Hsnap
    · simp only [bwalSnap]
      iframe «$a0» Hnil
      iunfold smOpt; iright; iexact Hmd
    wp_apply (wp_Apply ms γs memStorEmpty «$a0_ptr» (bwalSnap v.pos' cs) eood rfl Hpos) $$ [Hms Hsnap]
      as %err Hpost
    · iframe #; iframe Hms Hsnap
    icases Hpost with ⟨-, (⟨%Hood, -⟩ | ⟨-, Hms⟩)⟩
    · exact Hood.elim
    (try wp_auto)
    rw [show memStorApplied (bwalSnap v.pos' cs) = bwalBase v.pos' v.confstate' cs by
      simp [bwalBase, Hcp]]
  all_goals
    -- `if wal.st != nil { s.SetHardState(wal.st) }`: either way the meta is at `hs`
    by_cases Hsn : v.st' = null
    case' pos =>
      rw [decide_eq_true Hsn]
      simp only [Bool.not_true]
      (try wp_auto)
      iunfold hsOpt at Hst
      icases Hst with (⟨%H1, %H2⟩ | Hro)
      rotate_left
      · iunfold hsRO at Hro
        icases Hro with ⟨%pt, %pv, %pc, %uf, %Hnn, -⟩
        exact absurd Hsn Hnn
      subst H2
    case' neg =>
      rw [decide_eq_false Hsn]
      simp only [Bool.not_false]
      (try wp_auto)
      wp_apply (wp_SetHS ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) v.st' hs) $$ [Hmeta]
        as Hmeta
      · iframe #; iframe Hmeta
      (try wp_auto)
    all_goals
      -- `if len(wal.ents) != 0 { s.Append(wal.ents) }`
      iunfold entsPts at Hents
      icases Hents with ⟨%ls, Hs, #Hl⟩
      ihave %Hlen := ownSlice_len _ _ _ $$ Hs
      ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hl
      ihave Hents : entsPts v.ents' dq p $$ [Hs]
      · iunfold entsPts; iexists ls; iframe Hs Hl
      by_cases Hp : p = []
      · subst Hp
        have Hlen0 : v.ents'.len = W64 0 := by
          simp at Hl2
          subst Hl2
          simp at Hlen
          word
        rw [decide_eq_true Hlen0]
        simp only [Bool.not_true]
        (try wp_auto)
        ihave Hpos : w.[bootstrappedWAL, go!"pos"] ↦{dqw} v.pos' $$ [IndexP TermP]
        · iapply typedPointsto_combine _ _ _ Hpnn
          simp only [TypedPointsto.typedPointstoDef, named]
          iframe
        ihave Hw : w ↦{dqw} v $$ [lgW haveWALW Hpos confstateW wW stW entsW meta'W]
        · iapply typedPointsto_combine _ _ _ Hwnn
          simp only [TypedPointsto.typedPointstoDef, named]
          iframe
        iapply HΦ
        iexists γs
        rw [bwalStor_nil]
        iframe
      · have Hlen0 : ¬ v.ents'.len = W64 0 := by
          intro h
          apply Hp
          rw [h] at Hlen
          apply List.eq_nil_of_length_eq_zero
          rw [← Hl2, Hlen.1]
          rfl
        rw [decide_eq_false Hlen0]
        simp only [Bool.not_false]
        (try wp_auto)
        imod memStorage_handout ms γs (bwalBase v.pos' v.confstate' cs) p
          ⟨(bwalBase_ents_pend _ _ _).2, bwalBase_pendOk _ _ _ p Hp Hhead⟩ $$ Hms
          with ⟨Hms, Htok⟩
        wp_apply_core (wp_Append ms γs (bwalBase v.pos' v.confstate' cs) p v.ents' dq Hlast)
          $$ [Htok Hents]
        · iframe #; iframe Hents
          iright; iexact Htok
        iintro ⟨Hrcpt, Hents⟩
        icases Hrcpt with (%H | Hrcpt)
        · exact absurd H Hp
        imod memStorage_absorb ms γs { bwalBase v.pos' v.confstate' cs with pend := p }
          (bwalBase v.pos' v.confstate' cs) p $$ Hms Hrcpt
          with ⟨-, Hms⟩
        rw [bwalStor_absorb]
        (try wp_auto)
        ihave Hpos : w.[bootstrappedWAL, go!"pos"] ↦{dqw} v.pos' $$ [IndexP TermP]
        · iapply typedPointsto_combine _ _ _ Hpnn
          simp only [TypedPointsto.typedPointstoDef, named]
          iframe
        ihave Hw : w ↦{dqw} v $$ [lgW haveWALW Hpos confstateW wW stW entsW meta'W]
        · iapply typedPointsto_combine _ _ _ Hwnn
          simp only [TypedPointsto.typedPointstoDef, named]
          iframe
        iapply HΦ
        iexists γs
        iframe


end proof

end EtcdGrove
end Perennial
