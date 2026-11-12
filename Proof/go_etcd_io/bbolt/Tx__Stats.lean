/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Stats.lean` (U5, `notes/bbolt-proof-plan.md`): a done
transaction's statistics are a persistent points-to (`txDone`), read.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Stats
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.Stats.wp_proof : Tx.Stats.spec (GF := GF) (hG := hG) := by
  intro _ tx
  wp_start as Hd
  unfold txDone txDoneDef
  icases Hd with ⟨%s, #Hs⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
