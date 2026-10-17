/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__ReleaseSnapDBs.lean`.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046` only). The loop
over the directory's names keeps the snapshot and the directory handle; for a name whose index
is below the snapshot's, the `isPendingDB` check's atomic update is the caller's hook, which
gives the right to remove the file when the index is not pending.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__ReleaseSnapDBs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter__isPendingDB
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.os.Open
public import Spec.os.File__Readdirnames
public import Spec.os.File__Close
public import Spec.os.Remove
public import Spec.os.IsNotExist
public import Spec.strings.HasSuffix
public import Spec.strings.TrimSuffix
public import Spec.strconv.ParseUint
public import Spec.path.filepath.Base
public import Spec.path.filepath.Join
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.String

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.raft.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem snap.Snapshotter.ReleaseSnapDBs.wp_proof
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_isPendingDB : snap.Snapshotter.isPendingDB.spec (GF := GF) (hG := hG))
    (wp_Open : os.Open.spec (GF := GF) (hG := hG))
    (wp_Readdirnames : os.File.Readdirnames.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.spec (GF := GF) (hG := hG))
    (wp_IsNotExist : os.IsNotExist.spec (GF := GF) (hG := hG))
    (wp_HasSuffix : strings.HasSuffix.spec (GF := GF) (hG := hG))
    (wp_TrimSuffix : strings.TrimSuffix.spec (GF := GF) (hG := hG))
    (wp_ParseUint : strconv.ParseUint.spec (GF := GF) (hG := hG))
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    snap.Snapshotter.ReleaseSnapDBs.spec (GF := GF) (hG := hG) := by
  intro s γ dir snap dq sm
  wp_start as ⟨#Hs, Hsnap, #Hhook⟩
  ihave #Hs' := Hs
  iunfold isSnapshotter at Hs'
  icases Hs' with ⟨%mref, %lg, #Hm, #Hlg, %Hlgnn, #Hdir, #Hfs, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_Open as %f %err Hres
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, Hdh⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    wp_auto
    iapply HΦ
    iframe
    iunfold fsResult
    iright
    iexists e
    iframe #
    ipureintro; rfl
  subst Herr
  wp_auto
  wp_apply wp_Readdirnames $$ [$Hdh] as %sl %err2 ⟨Hdh, ⟨%names, #Hnames⟩, Hres⟩
  iunfold fsResult at Hres
  icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
  rotate_left
  · subst Herr
    wp_auto
    wp_apply wp_Close $$ [$Hdh] as %cerr -
    iapply HΦ
    iframe
    iunfold fsResult
    iright
    iexists e
    iframe #
    ipureintro; rfl
  subst Herr
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hnames
  ihave IH : iprop(∃ (n : w64) (v : GoString),
      "i" ∷ i_ptr ↦ n ∗ "filename" ∷ filename_ptr ↦ v ∗ "Hsnap" ∷ ownSnapM snap dq sm ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i filename Hsnap]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have Hlt' : sint.Z n < sint.Z sl.len := by simpa using Hif
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hlt'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    have Hlt : (sint.Z n).toNat < names.length := by rw [Hlen.1]; word
    obtain ⟨name, Hname⟩ : ∃ name, names[(sint.Z n).toNat]? = some name :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z n) names DFrac.discard name Hn $$ [Hnames] as -
    · iframe Hnames; ipureintro; exact Hname
    (try wp_auto)
    wp_apply wp_HasSuffix as %b -
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, name
      iframe
      ipureintro; word
    · (try wp_auto)
      wp_apply wp_Base
      wp_apply wp_TrimSuffix
      wp_apply wp_ParseUint as %idx %perr Hres
      iunfold fsResult at Hres
      icases Hres with (⟨%Herr, %Hparse⟩ | ⟨%e, %Herr, #He, -⟩)
      rotate_left
      · subst Herr
        wp_auto
        wp_apply wp_String as %f1 -
        iunfold fmt.stringMethodSpec at He
        wp_apply He as %str
        wp_apply wp_String as %f2 -
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨Hfsl, -⟩
        wp_auto
        wp_apply wp_Error
        · ipureintro; exact Hlgnn
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, name
        iframe
        ipureintro; word
      subst Herr
      wp_auto
      iunfold ownSnapM at Hsnap
      icases Hsnap with ⟨%ds, %pm, %uf, Hsnap⟩
      iNamed Hsnap
      wp_auto
      wp_apply wp_GetIndex $$ [$Hm] as Hm
      ihave Hsnap : ownSnapM snap dq sm $$ [HD Hd HM Hm Hpb]
      · iunfold ownSnapM
        iexists ds, pm, uf
        simp only [named]
        iframe
        isplitr
        · ipureintro; exact Hnn
        iexact Hpb
      wp_if_destruct
      · -- below the snapshot's index: the pending check, with the caller's hook
        wp_apply wp_isPendingDB $$ [$Hs]
        ihave Hh : iprop(|={⊤,∅}=> ∃ M, snapPending γ M ∗
              (snapPending γ M ={∅,⊤}=∗ (⌜M !! idx = none⌝ -∗ fs.removable (fs.join [dir, name])))) $$ [Hhook]
        · iunfold snapRemoveHook at Hhook
          icases Hhook with #Hhook
          iapply Hhook
          · ipureintro; exact Hparse
          · ipureintro; exact Hif
        simp only [LawfulSet.diff_empty]
        imod Hh with ⟨%M, HM, Hclose⟩
        imodintro
        iexists M
        iframe HM
        iintro HM
        imod Hclose $$ HM with Hrm
        imodintro
        iintro -
        cases hM : M !! idx with
        | some u =>
          -- pending: skipped
          simp only [Option.isSome_some, decide_true]
          wp_auto
          wp_apply wp_String as %f3 -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨Hfsl, -⟩
          wp_auto
          wp_apply wp_Info
          · ipureintro; exact Hlgnn
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, name
          iframe
          ipureintro; word
        | none =>
          -- not pending: the hook gave the right to remove `dir/name`
          ihave Hrm := Hrm $$ %rfl
          simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
          wp_auto
          wp_apply wp_String as %f3 -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨Hfsl, -⟩
          wp_auto
          wp_apply wp_Info
          · ipureintro; exact Hlgnn
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %psl ⟨Hpsl, -⟩
          wp_apply wp_Join $$ [$Hpsl] as %path ⟨%Hpath, -⟩
          subst Hpath
          have Hxs : ([dir, zero_val GoString].set (sint.nat (W64 (0 + 1))) name) = [dir, name] := by
            first | rfl | simp | decide
          rw [Hxs]
          wp_apply wp_Remove $$ [$Hrm] as %rmErr Hres
          iunfold fsResult at Hres
          icases Hres with (⟨%Herr, -⟩ | ⟨%e, %Herr, #He, -⟩)
          · subst Herr
            wp_auto
            wp_for_post
            iframe
            iexists n + W64 1, name
            iframe
            ipureintro; word
          · subst Herr
            wp_auto
            wp_apply wp_IsNotExist as %nb -
            cases nb
            · (try wp_auto)
              wp_apply wp_String as %f4 -
              iunfold fmt.stringMethodSpec at He
              wp_apply He as %str
              wp_apply wp_String as %f5 -
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %esl ⟨Hesl, -⟩
              wp_auto
              wp_apply wp_Error
              · ipureintro; exact Hlgnn
              (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, name
              iframe
              ipureintro; word
            · (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, name
              iframe
              ipureintro; word
      · wp_for_post
        iframe
        iexists n + W64 1, name
        iframe
        ipureintro; word

  · have Hge : ¬ sint.Z n < sint.Z sl.len := by simpa using Hif
    (try simp [Hge])
    (try wp_auto)
    wp_apply wp_Close $$ [$Hdh] as %cerr -
    iapply HΦ
    iframe
    iunfold fsResult
    ileft
    ipureintro; trivial

end proof

end EtcdGrove
end Perennial
