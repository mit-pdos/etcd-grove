/- The missing ConfState key on a pre-3.5 backend selects membership recovery. -/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapshotCindex
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : schema.Assumptions] [backend_sem : backend.Assumptions]

theorem snapshot_confState_absent
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (lg sp tx : Loc) (γ : GName) (γd : DBNames) (D : Data) (q : Qp)
    (habs : dget D schema.metaName go!"confState" = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapAt sp γ tx γd ∗ txLive tx γd q (bbolt.TxView.ro D) }}
      (App (App (Val (@! schema.UnsafeConfStateFromBackend)) (Val #lg))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp)))
    {{ RET #null; txLive tx γd q (bbolt.TxView.ro D) }} := by
  wp_start as ⟨#Hsp, Htx⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%bk, #Hmeta, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%key, #Hkey, #Hbytes⟩⟩
  ihave #Hb := mvcc.meta_isBucket hID hName hSafe bk $$ [$Hpkg $Hmeta]
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

theorem snapshot_confState_absent_open
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (lg sp : Loc) (γ : GName) (D : Data) (q : Qp)
    (habs : dget D schema.metaName go!"confState" = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ snapOpenQ sp D γ q }}
      (App (App (Val (@! schema.UnsafeConfStateFromBackend)) (Val #lg))
        (Val #(interface.mkOk (go.GoType.PointerType snapshot.ty) #sp)))
    {{ RET #null; snapOpenQ sp D γ q }} := by
  iintro %Φ ⟨#Hschema, #Hbe, Hsnap⟩ HΦ
  iunfold snapOpenQ at Hsnap
  icases Hsnap with ⟨%tx, %γd, #Hfields, Hshare, Htx⟩
  wp_apply snapshot_confState_absent hUR hID hName hSafe lg sp tx γ γd D q habs
    $$ [$Hschema $Hbe $Hfields $Htx] as Htx
  iapply HΦ
  iunfold snapOpenQ
  iexists tx, γd
  iframe Hfields Hshare Htx

end EtcdGrove
end Perennial
