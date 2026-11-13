/-
The proofs of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__cutPre.lean` (W2): W4's `walPreIn`
as `walPreInL`'s instance at one lock (`walPreIn_L`), W4's `WAL.sync.specPre` from `specPreL`
(`WAL.sync.specPre_of_L`), and `WAL.saveState.specPre` over `encoder.encode.specG` and the client's
laws of `raft.IsEmptyHardState`/`pbutil.MustMarshalMessage` (hypotheses: neither is proved over
`P.hsIn`, and `encode.specG` not yet over `io.writerStreamP`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- W4's pre-rename handle is the one-lock instance. -/
theorem walPreIn_L (w lg : Loc) (dir : GoString) (mds : GoSlice) (md : List w8) (e lt f : Loc)
    (snapi enti : w64) :
    walPreIn (GF := GF) w lg dir mds md e lt f snapi enti ⊣⊢
      walPreInL (GF := GF) w lg dir mds md e [lt] lt f snapi enti := by
  unfold walPreIn walPreInL
  constructor
  · iintro ⟨%locks, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14⟩
    iexists locks
    iframe
    ipureintro; rfl
  · iintro ⟨%locks, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, -, H15⟩
    iexists locks
    iframe

/-- **W4's `sync.specPre` is `specPreL` at one lock.** -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre_of_L
    (h : go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPreL (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.sync.specPre (GF := GF) (hG := hG) := by
  intro w lg dir mds md e lt f snapi enti W B S lim out pend c hlim hS
  iintro #Hw
  imodintro
  iintro %Φ ⟨#Henv, Hp, He, Hout⟩ HΦ
  iapply h w lg dir mds md e [lt] lt f snapi enti W B S lim out pend c hlim hS $$ Hw [Hp He Hout]
  · iframe Henv He Hout
    iapply (walPreIn_L w lg dir mds md e lt f snapi enti).1 $$ Hp
  · inext
    iintro %err ⟨Hp, He, Hr⟩
    iapply HΦ
    iframe He Hr
    iapply (walPreIn_L w lg dir mds md e lt f snapi enti).2 $$ Hp

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.wp_proofPre (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_empty : WalPbIn.IsEmptyLaw (GF := GF) (hG := hG) P)
    (wp_marshal : WalPbIn.MarshalHsLaw (GF := GF) (hG := hG) P Mr)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specG (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.saveState.specPre (GF := GF) (hG := hG) P Mr := by
  intro w e sp0 hp hs wi W B ok out pend c hok hne
  iintro #Hw
  wp_start as ⟨#Henv, Hst, Hen, He, Hout, #Hhs⟩
  try wp_auto
  wp_apply (wp_empty hp hs) $$ [] as %b %hb
  · iexact Hhs
  cases b
  case true =>
    -- empty: nothing
    try wp_auto
    iapply HΦ
    iframe Hen
    ileft
    iframe Hst He Hout
    ipureintro
    exact ⟨rfl, hb.1 rfl⟩
  have hne' : ¬ hsEmptyP hs := fun h => Bool.false_ne_true (hb.2 h)
  obtain ⟨hok', hsz⟩ := hne hne'
  try wp_auto
  wp_apply (wp_marshal hp hs hne') $$ [] as %d ⟨Hd, %Hdn⟩
  · iexact Hhs
  imod ownSlice_persist $$ Hd with #Hd
  unfold go_etcd_io.etcd.server.v3.storage.wal.StateType
  try wp_auto
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ «$v0» with #Ht
  ihave #Henc := wp_encode e wi W B ok out pend c «$r0_ptr» stateType (Mr.encState hs) hsz hok hok' $$ Hw
  wp_apply Henc $$ [He Hout «$r0»] as %err ⟨%pend', He, -, Hr⟩
  · iframe Henv He Hout
    iunfold encRecIn
    iexists _
    iframe «$r0»
    have hd : (recOf ⟨stateType, 0#32, Mr.encState hs⟩).data = some (Mr.encState hs) := by
      simp [recOf, stateType, crcType]
    simp only [hd, recBytes]
    have hst : stateType = W64 3 := rfl
    rw [hst]
    isplitl
    · iexact Ht
    isplitr
    · isplitr
      · ipureintro; exact Hdn
      · iexact Hd
    · ipureintro; trivial
  try wp_auto
  iapply HΦ
  iframe Hen
  iright
  iframe Hst
  isplitr
  · ipureintro; exact hne'
  iexists pend'
  iframe He
  unfold stateFrame
  iexact Hr

end proof

end EtcdGrove
end Perennial
