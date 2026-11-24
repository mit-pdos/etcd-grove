/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__saveStateNoErr.lean`: `WAL__saveState.lean`'s
over `encodeState.specNoErr`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveStateNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__encodeStateNoErr
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle

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
variable {Sio : IoSet} [FsStepSat (NoIoErr Sio)]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.wp_proofNoErr (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_encodeState : go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.specNoErr (Sio := Sio) (W := W) P Mr)
    (wp_empty : WalPbIn.IsEmptyLaw (GF := GF) (hG := hG) P) (wp_marshal : WalPbIn.MarshalHsLaw P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.specNoErr (Sio := Sio) (W := W) P Mr := by
  intro hS0 R jr r w dir h hp hs hpre hroom
  wp_start as ⟨#Harea, Hh, #Hhs, %Hhp⟩
  icases WalFs.walHandleIn_pkgInit P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hwpk0⟩
  try wp_auto
  wp_apply (wp_empty hp hs) $$ [] as %b %hb
  · iexact Hhs
  cases b
  case true =>
    try wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    ileft
    iframe Hh
    ipureintro
    exact hb.1 rfl
  have hne : ¬ hsEmptyP hs := fun h => Bool.false_ne_true (hb.2 h)
  obtain ⟨hrest, hx, hidx1⟩ := hpre hne
  ihave #HstIn : walStIn P Mr hp hs $$ []
  · iapply walStIn_intro P Mr hp hs false Hhp
    iframe Hhs
    unfold walStMarsh
    iintro !> %Φ' #Hpk Hk
    iapply (wp_marshal hp hs hne) $$ [Hpk]
    · iframe Hhs Hpk
    inext
    iintro %d ⟨Hd, %Hdn⟩
    iapply Hk $$ [Hd]
    · iexact Hd
    · ipureintro; exact Hdn
  try wp_auto
  wp_apply (wp_encodeState hS0 R jr r w dir h hp hs hrest hx hidx1 hroom) $$ [Hh] as %err ⟨%he, Hr⟩
  · iframe Harea Hh HstIn
    ipureintro; exact Hhp
  try wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact he
  iright
  isplitr
  · ipureintro; exact hne
  iexact Hr

end proof

end EtcdGrove
end Perennial
