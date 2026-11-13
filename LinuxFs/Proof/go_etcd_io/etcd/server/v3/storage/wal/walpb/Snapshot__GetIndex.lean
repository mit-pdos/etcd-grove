/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/walpb/Snapshot__GetIndex.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG) := by
  intro sp sm cs
  wp_start as Hs
  iunfold walSnapAt at Hs
  icases Hs with ⟨%s, #Hsp, #Hi, #Ht, %Hcs⟩
  ihave %Hn := typedPointsto_not_null sp _ _ $$ Hsp
  ihave %Hin := typedPointsto_not_null s.Index' _ _ $$ Hi
  iStructNamed Hsp
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  wp_if_destruct
  · exact absurd (by simpa using Hif) Hin
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
