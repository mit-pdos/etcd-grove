/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/encoder__flush.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__flush
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__Flush
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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

theorem go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Flush : go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Flush.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.encoder.flush.spec (GF := GF) (hG := hG) := by
  intro e wi W B lim out pend c hlim
  iintro #Hw
  wp_start as ⟨#Henv, He, Hout⟩
  iunfold encEnv at Henv
  icases Henv with ⟨#Hproto, #Hbin, #Hsync, #Htime, #Hmet⟩
  iunfold ownEncoder at He
  icases He with ⟨%pw, %h, %b, %u, %bs, %us, #Hmu, Hbw, Hpw, Hcrc, Hdig, Hbuf, Hbs, %Hb, Hu64, Hus,
    %Hus⟩
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply wp_Lock $$ [] as ⟨Hown, -⟩
  · iexact Hmu
  try wp_auto
  wp_apply (wp_Flush pw wi W B lim out pend hlim) $$ [Hw] [Hpw Hout] as %err ⟨Hpw, Hres⟩
  · iexact Hw
  · iframe
  try wp_auto
  wp_apply wp_Unlock $$ [Hown]
  · iframe
    isplitl []
    · iexact Hmu
    inext; itrivial
  try wp_auto
  iapply HΦ
  iframe Hres
  iunfold ownEncoder
  iexists pw, h, b, u, bs, us
  iframe
  iframe Hmu
  ipureintro
  exact ⟨Hb, Hus⟩

end proof

end EtcdGrove
end Perennial
