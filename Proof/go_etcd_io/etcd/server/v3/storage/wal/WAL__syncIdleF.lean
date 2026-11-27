/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__syncIdleF.lean`: `WAL__syncIdle.lean`'s, with
the encoder's `flush` when there is one (nothing pending: no `Write`, `encoder.flush.specPNE` over a writer
accepting only the empty stream). Unit `closefailed`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__syncIdleF
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.FdatasyncIdle
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Duration
public import Spec.time.Duration__Seconds_ptr
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [syscall_sem : syscall.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.wp_proofIdleF
    (Mr : WalMarshal)
    (wp_flush : go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.specPNE (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specIdleF (W := W) Mr := by
  intro R jr r w lg locks ls lt f fd name dir i I j X hj b fl m bs e hb hi hlen
  wp_start as ⟨#Harea, He, Henc, Hns, Hlg, #Hzap, Hlocks, Hls, #Hltf, #Henv, Hf, Hfd, Hk, HI, %hiI, Hn, Htf,
    Hcf, Hm, Hb⟩
  ihave #Hzpk : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  -- the encoder: nil, or one with nothing pending, whose `flush` writes nothing
  ihave Hws : io.writerStreamPNE (GF := GF) (wal.fileWi f) (fun ys => ys = []) (fun _ => iprop(True))
      (fun _ _ => iprop(False)) $$ []
  · unfold io.writerStreamPNE
    imodintro
    iintro %out %p %xs %dq %hok %hne
    exact absurd (List.append_eq_nil_iff.1 hok).2 hne
  by_cases hen : e = null
  subst hen
  wp_auto
  rotate_left
  icases Henc with (%he0 | ⟨%c, Henc⟩)
  · exact absurd he0 hen
  wp_auto
  simp only [decide_eq_false hen]
  wp_auto
  wp_apply (wp_flush e (wal.fileWi f) (fun _ => iprop(True)) (fun _ _ => iprop(False)) (fun ys => ys = [])
      [] [] c (fun xs ys h hy => by subst hy; exact List.prefix_nil.1 h) rfl) $$ [Hws] [Henc]
      as %err ⟨Henc, Hres⟩
  · iexact Hws
  · iframe; iframe #
  icases Hres with (⟨%Herr, -⟩ | ⟨-, -, Hfalse⟩)
  all_goals first | (iexfalso; iexact Hfalse) | skip
  subst Herr
  wp_auto
  ihave Henc : (⌜e = null⌝ ∨ ∃ c : w32, ownEncoder e (wal.fileWi f) c []) $$ [Henc]
  · iright; iexists c; iexact Henc
  all_goals try wp_auto
  all_goals (
    ihave #Henv0 := Henv
    iunfold encEnv at Henv0
    icases Henv0 with ⟨#Hproto, #Hbin, #Hsync, #Htime, #Hmet⟩
    iunfold wal.metricsInit at Hmet
    icases Hmet with ⟨⟨%hs, #Hhs, #Hhspec⟩, -, -⟩
    iunfold wal.histSpec at Hhspec
    wp_apply wp_Now as %t -
    wp_apply (wp_tail w locks ls lt (DFrac.own 1) (DFrac.own 1)) $$ [Hlocks Hls] as ⟨Hlocks, Hls⟩
    · iframe
    ihave #Hlt0 := Hltf
    iunfold fileutil.lockedFile at Hlt0
    iStructNamed Hlt0
    wp_auto
    wp_apply (fileutil.Fdatasync.wp_idle wp_Fd Mr R jr r f fd name dir i I hiI j X hj b m bs (DFrac.own 1)
        (DFrac.own 1) fl hb hi hlen) $$ [Hf Hfd Hk HI Hn Htf Hcf Hm Hb]
        as %en ⟨Hf, Hfd, Hk, HI, Hn, Htf, Hcf, Hsy⟩
    · iframe; iexact Harea
    wp_apply wp_Since as %dur -
    try wp_auto
    by_cases Hif : sint.Z (W64 1000000000) < sint.Z dur
    all_goals first | simp only [decide_eq_true Hif] | simp only [decide_eq_false Hif]
    all_goals (wp_pures; try wp_auto)
    · wp_apply wp_Duration as %f1 -
      wp_apply wp_Duration as %f2 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      try wp_auto
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #
      try wp_auto
      wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl' took
      · iframe
      try wp_auto
      wp_apply Hhspec
      try wp_auto
      iapply HΦ
      iframe He Henc Hns Hlg Hlocks Hls Hf Hfd Hk HI Hn Htf Hcf
      isplitr
      · ipureintro; exact hiI
      icases Hsy with (⟨%H0, Hm, Hb⟩ | ⟨%H0, Hm, Hb⟩)
      · ileft; iframe Hm Hb; ipureintro; subst H0; rfl
      · iright; iframe Hm Hb; ipureintro; unfold errnoErr; simp; exact H0
    · try wp_auto
      wp_apply (wp_Seconds_ptr _ dur) $$ [took] as %fl' took
      · iframe
      try wp_auto
      wp_apply Hhspec
      try wp_auto
      iapply HΦ
      iframe He Henc Hns Hlg Hlocks Hls Hf Hfd Hk HI Hn Htf Hcf
      isplitr
      · ipureintro; exact hiI
      icases Hsy with (⟨%H0, Hm, Hb⟩ | ⟨%H0, Hm, Hb⟩)
      · ileft; iframe Hm Hb; ipureintro; subst H0; rfl
      · iright; iframe Hm Hb; ipureintro; unfold errnoErr; simp; exact H0)

end proof

end EtcdGrove
end Perennial
