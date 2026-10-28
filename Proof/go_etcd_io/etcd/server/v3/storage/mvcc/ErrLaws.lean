/-
Laws of mvcc's error variables, for clients outside the package: they take what they need of an
error variable from here instead of destructuring `mvccInit` (`Base.lean`), whose conjuncts move
when a variable is added. (The compactor pilot's phase 3, 2026-10-27: its `Run` proofs reached
`ErrCompacted` by `mvccInit`'s 31st conjunct.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`ErrCompacted`** is a fixed pointer error, which `errors.Is` can take as a target: the cell
holds it (read-only), and it is a pointer error (`errors.New`'s `*errorString`). -/
theorem mvcc.ErrCompacted_target :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
      ∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok e ∗
        ⌜_root_.Perennial.errors.IsPointerError e⌝ := by
  iintro #Hp
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hp
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HnvC, -⟩
  iunfold EtcdGrove.errorsNewVar at HnvC
  icases HnvC with ⟨%x, #Hx, -⟩
  iexists _
  iframe Hx
  ipureintro
  exact (EtcdGrove.errorString_leaf x).1

end laws

end EtcdGrove
end Perennial
