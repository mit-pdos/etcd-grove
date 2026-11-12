/-
The writer's view's base is a mapped address (`wtxW_base_pos`): the premise `0 < v.base.addr`
of `node.put`/`node.del`/`node.childIndex` (`notes/bbolt-proof-plan.md`, batch 30). A module of
its own so that adding it rebuilds no importer of `Inv/Ctx`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section ctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The writer's view's base is a mapped address (`mapFields`' mapped case). -/
theorem wtxW_base_pos (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜0 < X.v.base.addr⌝ := by
  unfold wtxW mapFields
  iintro ⟨-, -, %l, ⟨-, -, -, -, %H⟩, -⟩
  ipureintro; exact H.2.1

end ctx

end bbolt
end EtcdGrove
end Perennial
