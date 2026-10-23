/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__createMergedSnapshotMessage.lean`.
Lean-first (no Rocq counterpart); D22 S-h, 2026-10-20.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newSnapshotReaderCloser
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.NewMessage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `proto.Clone` of a nil-or-read-only conf state: a fresh one holding the same, owned (nil for
nil). -/
theorem wp_clone_csOpt (hClone : proto.CloneConfState.spec (GF := GF) (hG := hG)) (cs : Loc)
    (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
        csOpt cs DFrac.discard c }}
      (App (Val (@! google_golang_org.protobuf.proto.Clone))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfState.ty) #cs)))
    {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfState.ty) #p');
        csOpt p' (DFrac.own 1) c }} := by
  iintro %Φ ⟨#Hpkg, #Hc⟩ HΦ
  iunfold csOpt at Hc
  icases Hc with (⟨%Hn, %Hce⟩ | #Hc)
  · subst Hn Hce
    wp_apply hClone.2
    iapply HΦ
    iunfold csOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · wp_apply hClone.1 cs DFrac.discard c $$ [] as %p' ⟨-, Hp'⟩
    · iframe #
    iapply HΦ
    iunfold csOpt
    iright; iexact Hp'

theorem EtcdServer.createMergedSnapshotMessage.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hNSR : newSnapshotReaderCloser.spec (GF := GF) (hG := hG))
    (hClone : proto.CloneConfState.spec (GF := GF) (hG := hG))
    (hSize : backend.snapshot.Size.spec (GF := GF) (hG := hG))
    (hNM : snap.NewMessage.spec (GF := GF) (hG := hG)) :
    EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG) := by
  intro s ml st snapt snapi cs lg kv be RC RC' RS RS' Qd
  wp_start as ⟨#Hlgf, %Hlgnn, Hlr, #Hkvf, Hkc, HRC, #Hbef, Hbs, HRS, Hm, #Hcs⟩
  (try wp_auto)
  wp_apply hLg s lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hKV s kv $$ []
  · iframe #
  iunfold srvKVCommitOk at Hkc
  icases Hkc with ⟨%ki, %Hki, #Hcommit⟩
  subst Hki
  (try wp_auto)
  -- `s.KV().Commit()`
  wp_bind (App (Val #(methods ki.ty go!"Commit" ki.v)) (Val #()))
  iapply Hcommit $$ HRC
  inext
  iintro HRC'
  -- (D22 the stored-index window, 2026-10-23) what `Snapshot()` takes, from what `Commit()` gave
  ihave HRS := HRS $$ HRC'
  (try wp_auto)
  -- `s.be.Snapshot()`
  iunfold srvBeSnapOk at Hbs
  icases Hbs with ⟨%bi, %Hbi, #Hsnap⟩
  subst Hbi
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"Snapshot" bi.v)) (Val #()))
  iapply Hsnap $$ HRS
  inext
  iintro %sp %D ⟨Hsn, HRS', %HQ⟩
  iunfold backend.snapOpen at Hsn
  icases Hsn with ⟨%γd, Hsn⟩
  (try wp_auto)
  -- `newSnapshotReaderCloser(lg, dbsnap)`, with half of the snapshot (its `Size` read after)
  icases (backend.snapOpenQ_half sp D γd 1).1 $$ Hsn with ⟨Hsn1, Hsn2⟩
  wp_apply hNSR lg sp D γd $$ [Hsn1] as %rc Hrc
  · iframe #; iframe Hsn1; ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Pproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- `proto.Clone(confState)`: the clone holds `c`, owned (nil for nil)
  iunfold epCsOk at Hcs
  ihave #Hc : iprop(∃ c : ConfStateM, csOpt cs DFrac.discard c) $$ []
  · icases Hcs with (%Hn | ⟨%c, #Hc⟩)
    · iexists ConfStateM.mk [] [] [] [] false
      iunfold csOpt; ileft; ipureintro; exact ⟨Hn, rfl⟩
    · iexists c; iunfold csOpt; iright; iexact Hc
  icases Hc with ⟨%c, #Hc⟩
  wp_apply wp_clone_csOpt hClone cs c $$ [] as %p' Hp'
  · iframe #
  (try wp_auto)
  -- the merged metadata and snapshot (`&snapi`, `&snapt` frozen: nothing writes them after)
  imod cellRO_alloc snapi_ptr snapi $$ snapi with #cI
  imod cellRO_alloc snapt_ptr snapt $$ snapt with #cT
  imod smPts_of_struct «$v0_ptr»
    ({ state' := zeroValDef, ConfState' := p', Index' := snapi_ptr, Term' := snapt_ptr,
       unknownFields' := slice.nil, sizeCache' := 0 } : go_etcd_io.raft.v3.raftpb.SnapshotMetadata)
    (SnapshotMetadataM.mk c snapi snapt) ⊤ rfl
    $$ [«$v0» Hp'] with Hmd
  · iframe «$v0» Hp' cI cT
  ihave Hmdo : smOpt «$v0_ptr» (DFrac.own 1) (SnapshotMetadataM.mk c snapi snapt) $$ [Hmd]
  · iunfold smOpt; iright; iexact Hmd
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSnapM_of_struct «$r0_ptr»
    ({ state' := zeroValDef, Data' := slice.nil, Metadata' := «$v0_ptr», unknownFields' := slice.nil,
       sizeCache' := 0 } : go_etcd_io.raft.v3.raftpb.Snapshot)
    (SnapshotM.mk [] (SnapshotMetadataM.mk c snapi snapt)) ⊤ rfl
    $$ [«$r0» Hnil Hmdo] with Hsnp
  · iframe «$r0» Hnil Hmdo
  -- `m.Snapshot = snapshot`, the message then frozen
  icases msgOwn_store_Snapshot ml st $$ Hm with ⟨%ps, HSn, Hback⟩
  (try wp_auto)
  ihave Hm := Hback $$ %_ %(SnapshotM.mk [] (SnapshotMetadataM.mk c snapi snapt)) HSn Hsnp
  imod msgOwn_persist ml _ _ $$ Hm with #Hm
  -- `dbsnap.Size()`, with the sender's half, which then goes to the reader (the pipe's hand-over)
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_apply hSize sp D γd _ $$ [Hsn2] as %n Hsn2
  · iframe #; iframe Hsn2
  ihave Hrs := Hrc $$ Hsn2
  -- `snap.NewMessage(m, rc, size)`
  wp_apply hNM ml (mergedSt st c snapi snapt) rc n $$ [] as %mg ⟨#Hmi, %tsz, %cc, %γc, #Htsz, #Hcc, #Hccb⟩
  · simp only [mergedSt]; iexact Hm
  (try wp_auto)
  iapply HΦ
  simp only [mergedSt]
  iframe Hlr HRS'
  iexists rc, D, c
  iframe Hm Hc Hrs
  isplitr
  · iunfold mergedMsg
    iframe Hmi
    iexists tsz, cc, γc
    iframe Htsz Hcc Hccb
  ipureintro; exact HQ

end proof

end EtcdGrove
end Perennial
