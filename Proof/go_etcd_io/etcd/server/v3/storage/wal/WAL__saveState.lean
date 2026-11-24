/-
`(*WAL).saveState` over `encodeState` (the torn-`Save` fix, fork `2bd3048d7`, split the write off) and
`WalPbIn.IsEmptyLaw` (`IsEmptyHardState`, `WAL__cutPre.lean`'s): nothing for an empty state. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveState
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__encodeState
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

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_encodeState : go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.spec (W := W) P Mr)
    (wp_empty : WalPbIn.IsEmptyLaw (GF := GF) (hG := hG) P) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.spec (W := W) P Mr := by
  intro R jr r w dir h hp hs hpre
  wp_start as ⟨#Harea, Hh, #Hhs, %Hhp⟩
  icases WalFs.walHandleIn_pkgInit P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hwpk0⟩
  try wp_auto
  wp_apply (wp_empty hp hs) $$ [] as %b %hb
  · iexact Hhs
  cases b
  case true =>
    try wp_auto
    iapply HΦ
    ileft
    iframe Hh
    ipureintro
    exact ⟨rfl, hb.1 rfl⟩
  have hne : ¬ hsEmptyP hs := fun h => Bool.false_ne_true (hb.2 h)
  obtain ⟨hrest, hx, hidx1⟩ := hpre hne
  try wp_auto
  wp_apply (wp_encodeState R jr r w dir h hp hs hrest hx hidx1) $$ [Hh] as %err Hr
  · iframe Harea Hh Hhs
    ipureintro; exact Hhp
  icases Hr with (⟨%he, Hr⟩ | %he)
  · try wp_auto
    iapply HΦ
    iright; ileft
    isplitr
    · ipureintro; exact ⟨he, hne⟩
    iexact Hr
  · try wp_auto
    iapply HΦ
    iright; iright
    ipureintro; exact he

end proof

end EtcdGrove
end Perennial
