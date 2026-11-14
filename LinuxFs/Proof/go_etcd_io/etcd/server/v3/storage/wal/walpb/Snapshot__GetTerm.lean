/-
The proof of `walpb.Snapshot.GetTerm.spec` (stated in
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ReadAllCallees.lean`, with `ReadAll`'s other
callees), as `Snapshot__GetIndex.lean` proves `GetIndex`'s.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetTerm.spec (GF := GF) (hG := hG) := by
  intro sp s
  wp_start as Hs
  iunfold walSnapIdTerm at Hs
  icases Hs with ⟨%c, Hs, %hs⟩
  iunfold snapRoC at Hs
  icases Hs with ⟨%pi, %pt, %pc, %Hn, -, -, #Ht, Hct, -⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  have hs2 : s.2 = c.term.getD (W64 0) := by rw [← hs]; rfl
  rcases hct : c.term with _ | t
  · rw [hct] at hs2
    iunfold recCell at Hct
    icases Hct with %Hpt
    subst Hpt
    wp_auto
    rw [hs2]; simp only [Option.getD_none, Option.getD_some]
    iapply HΦ
    ipureintro; trivial
  · rw [hct] at hs2
    iunfold recCell at Hct
    ihave %Hn' := typedPointsto_not_null pt _ _ $$ Hct
    simp only [decide_eq_false Hn']
    wp_auto
    rw [hs2]; simp only [Option.getD_none, Option.getD_some]
    iapply HΦ
    ipureintro; trivial

end proof

end EtcdGrove
end Perennial
