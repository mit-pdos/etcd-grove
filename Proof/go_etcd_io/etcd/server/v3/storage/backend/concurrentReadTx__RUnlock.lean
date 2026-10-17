/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/concurrentReadTx__RUnlock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__finishWait

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.concurrentReadTx.RUnlock.wp_proof
    (hfw : backend.sharedBoltTx.finishWait.spec (GF := GF) (hG := hG)) :
    backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b crt rtx rv
  wp_start as H
  unfold crtSnap
  icases H with ⟨%m, %Pb, %cm, %tm, %wg, %γw, %γo, %γt, %k, %q, %rt, %cst, #Hrt, #Htm, -, #Hcst,
    -, -, -, #Hwg, Hown, #Hg, Hsh, #Hsnap, #Hintv, #Hwgi, %Hwf⟩
  wp_auto
  wp_apply hfw γ cst DFrac.discard rtx wg γw γo γt k q $$ [$Hwg $Hwgi $Hsh] as ⟨-, Htok⟩
  iapply HΦ
  unfold crTok
  iexists rt, tm
  iframe; iframe #


end proof

end EtcdGrove
end Perennial
