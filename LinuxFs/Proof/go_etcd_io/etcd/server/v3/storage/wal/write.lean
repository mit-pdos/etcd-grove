/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/write.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.write
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__Write
public import LinuxFs.Spec.time.Duration__Seconds
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Perennial.Proof.encoding.binary.PtrMethods

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.write.wp_proof
    (wp_PWrite : go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Write.spec (GF := GF) (hG := hG))
    (wp_Put : encoding.binary.littleEndian.PutUint64.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.write.spec (GF := GF) (hG := hG) := by
  intro pw wi W out pend u us d ds dq lenField hus hds
  iintro #Hw
  wp_start as ⟨#Henv, Hpw, Hout, Hu, Hd⟩
  iunfold encEnv at Henv
  icases Henv with ⟨#Hproto, #Hbin, #Hsync, #Htime, #Hmet⟩
  iunfold wal.metricsInit at Hmet
  icases Hmet with ⟨-, ⟨%hs, #Hhs, #Hhspec⟩, ⟨%g, #Hg, #Hgspec⟩⟩
  wp_auto
  wp_apply (encoding.binary.wp_LittleEndian_PutUint64_of wp_Put u us [] lenField hus) $$ [Hu] as Hu
  · rw [List.append_nil]; iexact Hu
  rw [List.append_nil]
  wp_apply wp_Now as %t -
  have h8 : (u64Le lenField).length < 2 ^ 62 := by rw [u64Le_length]; decide
  wp_apply (wp_PWrite pw wi W out pend u (u64Le lenField) (DFrac.own 1) h8) $$ [Hw] [Hpw Hout Hu]
    as %n %err ⟨%ys, %pend1, Hout, Hpw, Hu, %Hr⟩
  · iexact Hw
  · iframe
  iunfold wal.gaugeAddSpec at Hgspec
  iunfold wal.histSpec at Hhspec
  wp_apply Hgspec
  rcases err with ei | _
  · -- the length word's write failed
    obtain ⟨hp1, hys⟩ := Hr.2 (fun h => nomatch h)
    wp_auto
    iapply HΦ
    iexists ys, pend1
    iframe
    ipureintro
    exact ⟨fun h => (nomatch h), fun _ => ⟨hp1, hys.trans (by
      exact List.prefix_append _ _)⟩⟩
  have hr1 := (Hr.1 rfl).1
  wp_auto
  wp_apply (wp_PWrite pw wi W (out ++ ys) pend1 d ds dq hds) $$ [Hw] [Hpw Hout Hd]
    as %n2 %err2 ⟨%ys2, %pend2, Hout, Hpw, Hd, %Hr2⟩
  · iexact Hw
  · iframe
  wp_apply wp_Since as %dur -
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  try wp_auto
  wp_apply wp_Seconds as %fl -
  try wp_auto
  wp_apply Hhspec
  try wp_auto
  wp_apply Hgspec
  try wp_auto
  iapply HΦ
  iexists ys ++ ys2, pend2
  rw [← List.append_assoc]
  iframe
  ipureintro
  constructor
  · intro h
    rw [List.append_assoc, (Hr2.1 h).1, ← List.append_assoc, hr1, List.append_assoc]
  · intro h
    obtain ⟨hp2, hys2⟩ := Hr2.2 h
    refine ⟨hp2, ?_⟩
    have : ys ++ ys2 <+: ys ++ (pend1 ++ ds) := (List.prefix_append_right_inj _).2 hys2
    rw [← List.append_assoc, hr1, List.append_assoc] at this
    rwa [← List.append_assoc] at this

end proof

end EtcdGrove
end Perennial
