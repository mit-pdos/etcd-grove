/- The missing ConfState key on a pre-3.5 backend selects membership recovery. -/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapshotCindex
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : schema.snapshotmeta.Assumptions] [backend_sem : backend.Assumptions]

theorem snapshot_confState_absent
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (lg sp tx : Loc) (γ : GName) (γd : DBNames) (D : Data) (q : Qp) (bk : GoInterface) (key : GoSlice)
    (habs : dget D schema.metaName go!"confState" = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBucket bk mvcc.metaBI ∗
      key ↦*□ (go!"confState" : GoString) ∗
      snapAt sp γ tx γd ∗ txLive tx γd q (bbolt.TxView.ro D) }}
      (App (App (App (App (Val (@! schema.snapshotmeta.ReadConfState)) (Val #lg))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp))) (Val #bk)) (Val #key))
    {{ RET #null; txLive tx γd q (bbolt.TxView.ro D) }} := by
  wp_start as ⟨#Hb, #Hbytes, #Hsp, Htx⟩
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  (try wp_auto)
  wp_apply hUR sp tx γ γd D q bk mvcc.metaBI key slice.nil go!"confState" [] DFrac.discard DFrac.discard (W64 0)
    $$ [$Hsp $Htx $Hb $Hbytes $Hnil] as %ks %vs ⟨Htx, -, -, Hout⟩
  have hempty : ((D.lookup schema.metaName).map
      (fun b => cursorRange (bktEnts b) go!"confState" [] (W64 0))).getD [] = [] := by
    cases hb : D.lookup schema.metaName with
    | none => rfl
    | some b =>
      have hkey : b.lookup go!"confState" = none := by simpa [dget, hb] using habs
      simp only [Option.map_some, Option.getD_some]
      rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts, hkey]
  irevert Hout
  rw [hempty]
  iintro Hout
  imod kvsOutRd_nil ⊤ γd tx ks vs $$ Hout with ⟨#Hks, -⟩
  ihave %hlen := ownSlice_len _ _ _ $$ Hks
  have hzero : ks.len = W64 0 := by simp only [List.length_nil] at hlen; word
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ $$ Htx
  exact absurd hzero Hif

/-- The successful JSON read of a saved configuration into a fresh Go value. -/
def snapshotDecodesConfState (bytes : GoString) (P : Loc → IProp GF) : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (p : Loc),
      {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ sl ↦*{dq} bytes ∗ p ↦ zero_val raftpb.ConfState }}
        (App (App (Val (@! _root_.Perennial.encoding.json.Unmarshal)) (Val #sl))
          (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p)))
      {{ RET #GoInterface.nil; sl ↦*{dq} bytes ∗ P p }}

/-- Read the encoded configuration from the same transaction that streams the snapshot.
The decoder consumes precisely the bytes saved at the ConfState key. -/
theorem snapshot_confState_present
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (lg sp tx : Loc) (γ : GName) (γd : DBNames) (D : Data) (q : Qp) (bk : GoInterface) (key : GoSlice)
    (bytes : GoString) (P : Loc → IProp GF)
    (hval : dget D schema.metaName go!"confState" = some bytes)
    (hdecode : snapshotDecodesConfState bytes P) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBucket bk mvcc.metaBI ∗
      key ↦*□ (go!"confState" : GoString) ∗
      snapAt sp γ tx γd ∗ txLive tx γd q (bbolt.TxView.ro D) }}
      (App (App (App (App (Val (@! schema.snapshotmeta.ReadConfState)) (Val #lg))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp))) (Val #bk)) (Val #key))
    {{ (p : Loc), RET #p; txLive tx γd q (bbolt.TxView.ro D) ∗ P p }} := by
  wp_start as ⟨#Hb, #Hbytes, #Hsp, Htx⟩
  ihave #Hjson : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  (try wp_auto)
  wp_apply hUR sp tx γ γd D q bk mvcc.metaBI key slice.nil go!"confState" [] DFrac.discard DFrac.discard (W64 0)
    $$ [$Hsp $Htx $Hb $Hbytes $Hnil] as %ks %vs ⟨Htx, -, -, Hout⟩
  have hone : ((D.lookup schema.metaName).map
      (fun b => cursorRange (bktEnts b) go!"confState" [] (W64 0))).getD [] = [(go!"confState", bytes)] := by
    cases hb : D.lookup schema.metaName with
    | none => simp [dget, hb] at hval
    | some b =>
      have hk : b.lookup go!"confState" = some bytes := by simpa [dget, hb] using hval
      simp only [Option.map_some, Option.getD_some]
      rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts, hk]
  irevert Hout
  rw [hone]
  iintro Hout
  imod kvsOutRd_single ⊤ γd tx ks vs _ _ $$ Hout with ⟨%ksl, %sl, #Hks, -, #Hvs, #HbytesVal⟩
  ihave %hklen := ownSlice_len _ _ _ $$ Hks
  ihave %hvlen := ownSlice_len _ _ _ $$ Hvs
  have hkone : ks.len = W64 1 := by simp only [List.length_cons, List.length_nil] at hklen; word
  have hvpos : 0 ≤ sint.Z (0#64) ∧ sint.Z (0#64) < sint.Z vs.len := by
    simp only [List.length_cons, List.length_nil] at hvlen; word
  icases ownSlice_elem_acc (sint.Z (W64 0)) sl vs DFrac.discard [sl] (by decide) rfl $$ Hvs with ⟨#Hsl, -⟩
  icases rdB_acc γd tx sl bytes q _ $$ [$HbytesVal $Htx] with ⟨%dq, Hbs, Hclose⟩
  (try wp_auto)
  simp [hkone]
  (try wp_auto)
  simp [hkone]
  (try wp_auto)
  simp only [hvpos]
  (try simp only [show sint.Z (0#64) = (0 : Int) by decide])
  (try wp_auto)
  wp_apply hdecode sl dq confState_ptr $$ [$Hjson $Hbs $confState] as ⟨Hbs, HP⟩
  (try wp_auto)
  iapply HΦ
  iframe HP
  iapply Hclose $$ Hbs

theorem snapshot_confState_absent_open
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (lg sp : Loc) (γ : GName) (D : Data) (q : Qp) (bk : GoInterface) (key : GoSlice)
    (habs : dget D schema.metaName go!"confState" = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBucket bk mvcc.metaBI ∗
      key ↦*□ (go!"confState" : GoString) ∗ snapOpenQ sp D γ q }}
      (App (App (App (App (Val (@! schema.snapshotmeta.ReadConfState)) (Val #lg))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp))) (Val #bk)) (Val #key))
    {{ RET #null; snapOpenQ sp D γ q }} := by
  iintro %Φ ⟨#Hschema, #Hbe, #Hb, #Hbytes, Hsnap⟩ HΦ
  iunfold snapOpenQ at Hsnap
  icases Hsnap with ⟨%tx, %γd, #Hfields, Hshare, Htx⟩
  wp_apply snapshot_confState_absent hUR lg sp tx γ γd D q bk key habs
    $$ [$Hschema $Hbe $Hb $Hbytes $Hfields $Htx] as Htx
  iapply HΦ
  iunfold snapOpenQ
  iexists tx, γd
  iframe Hfields Hshare Htx

theorem snapshot_confState_present_open
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (lg sp : Loc) (γ : GName) (D : Data) (q : Qp) (bk : GoInterface) (key : GoSlice)
    (bytes : GoString) (P : Loc → IProp GF)
    (hval : dget D schema.metaName go!"confState" = some bytes)
    (hdecode : snapshotDecodesConfState bytes P) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBucket bk mvcc.metaBI ∗
      key ↦*□ (go!"confState" : GoString) ∗
      snapOpenQ sp D γ q }}
      (App (App (App (App (Val (@! schema.snapshotmeta.ReadConfState)) (Val #lg))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp))) (Val #bk)) (Val #key))
    {{ (p : Loc), RET #p; snapOpenQ sp D γ q ∗ P p }} := by
  iintro %Φ ⟨#Hschema, #Hbe, #Hb, #Hbytes, Hsnap⟩ HΦ
  iunfold snapOpenQ at Hsnap
  icases Hsnap with ⟨%tx, %γd, #Hfields, Hshare, Htx⟩
  wp_apply snapshot_confState_present hUR lg sp tx γ γd D q bk key bytes P hval hdecode
    $$ [$Hschema $Hbe $Hb $Hbytes $Hfields $Htx] as %p ⟨Htx, HP⟩
  iapply HΦ
  iframe HP
  iunfold snapOpenQ
  iexists tx, γd
  iframe Hfields Hshare Htx

end EtcdGrove
end Perennial
