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
  intro sp s
  wp_start as Hs
  iunfold walSnapIdTerm at Hs
  icases Hs with ⟨%md, %cs, Hs, %hs⟩
  iunfold walSnapAt at Hs
  icases Hs with ⟨%v, #Hp, #Hi, #Ht, %hc⟩
  ihave %Hn := typedPointsto_not_null sp _ _ $$ Hp
  ihave %Hn' := typedPointsto_not_null v.Index' _ _ $$ Hi
  ihave #Hp2 := Hp
  iStructNamed Hp2
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  simp only [decide_eq_false Hn']
  wp_auto
  rw [← hs]
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
