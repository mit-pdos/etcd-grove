/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/pipeline__start.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipeline__handle
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.WaitGroupAdd
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Perennial.Spec.sync.WaitGroup__Add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option maxHeartbeats 2000000 in
theorem rafthttp.pipeline.start.wp_proof
    (hHandle : rafthttp.pipeline.handle.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG)) :
    rafthttp.pipeline.start.spec (GF := GF) (hG := hG) := by
  intro Rh p to R
  wp_start as ⟨#Hf, ⟨%sc0, Hsc⟩, ⟨%mc0, Hmc⟩, Had, HR1, HR2, HR3, HR4⟩
  iunfold pipeFixed at Hf
  icases Hf with ⟨%tr, %pk, %ec, %lg, %urls, %uvs, %lid, %cid, %rt, %ps, %fs, %r, %id, %γd,
    #Htr, #Hpk, #Hec, #Hto, #Hlg, %Hlgnn, #Hurls, #Huvs, #Hlid, #Hcid, #Hrtf, #Hrt, #Hpick, #Hps,
    #Hpsok, #Hfs, #Hr, #Hraft⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply chan.wp_make1 (V := Unit) as %sc %γs ⟨#Hscc, %-, Hsco⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γs sc $$ Hscc Hsco with Hbc
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := Loc) (W64 64))
  · ipureintro; exact ⟨by decide, by decide⟩
  iintro %mc %γm ⟨#Hmcc, %Hcap, Hmo⟩
  simp only [show ¬ (W64 64 = W64 0) by decide, ↓reduceIte]
  imod start_bag (pipeMsg Rh to) _ mc γm (by trivial) $$ Hmcc Hmo with #Hbag
  (try wp_auto)
  ipersist Hsc
  ipersist Hmc
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γch, #Hint, Hown⟩
  ihave #Hunk : ownBroadcastChan sc γs iprop(True) .Unknown $$ []
  · iapply ownBroadcastChan_close _ _ _ _ γch
    isplit
    · iexact Hint
    · itrivial
  ihave Hbc := ownBroadcastChan_close sc γs iprop(True) .Pending γch $$ [$Hint $Hown]
  ihave #HhOk : pipeHandleOk Rh p to R $$ []
  · iunfold pipeHandleOk
    isplitr
    · iunfold pipeSenderOk
      iexists tr, pk, sc, ec, γs, lg, urls, uvs, lid, cid, rt
      iframe #
      ipureintro; exact Hlgnn
    · iexists ps, fs, r, id, γd, mc, γm
      iframe #
  wp_apply (wgJoin_wp_Add4_of wp_Add R _ _ _) $$ [$Had] as ⟨Had, Hd1, Hd2, Hd3, Hd4⟩
  · ipureintro; decide
  (try wp_auto)
  rw [show W32 0 + W32 4 = W32 4 by decide]
  ihave HI : (∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝ ∗
      "Hds" ∷ ([∗list] _u ∈ List.replicate (4 - sint.nat k) (),
        (sync.join.ownDone (p.[rafthttp.pipeline, go!"wg"]) R ∗ R))) $$ [i Hd1 Hd2 Hd3 Hd4 HR1 HR2 HR3 HR4]
  · iexists (W64 0)
    simp only [named]
    iframe
    isplitr
    · ipureintro; decide
    simp only [show 4 - sint.nat (W64 0) = 4 by decide, List.replicate_succ, List.replicate_zero]
    iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z k < 4 := by have := Hif; word
    have hk : 4 - sint.nat k = (3 - sint.nat k) + 1 := by word
    rw [hk, List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hds with ⟨⟨Hd, HR⟩, Hds⟩
    wp_apply wp_fork $$ [Hd HR]
    · (try wp_auto)
      wp_apply hHandle Rh p to R $$ [$HhOk $HR $Hd]
      ipureintro; exact isPanic_intoVal _
    (try wp_auto)
    wp_for_post
    iframe
    iexists (k + W64 1)
    simp only [named]
    iframe
    isplitr
    · ipureintro; constructor <;> word
    have hk1 : 4 - sint.nat (k + W64 1) = 3 - sint.nat k := by word
    rw [hk1]
    iframe
  -- the loop's end: `4` goroutines started; the log
  have Hk4 : sint.Z k = 4 := by have := Hif; word
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals try (
    wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls -
    wp_apply hZString as %f1 -
    wp_apply hIDStringPtr _ DFrac.discard to $$ [$Hto] as %ts -
    wp_apply hZString as %f2 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hInfo lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto))
  all_goals
    iapply HΦ
    iunfold pipeStarted
    iframe #
    iexists γs
    iframe

end proof

end EtcdGrove
end Perennial
