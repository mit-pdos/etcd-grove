/-
**etcd's backend opened as a storage** (M3, 2026-11-06; the design "mvcc's API over its storage
abstraction", approved by the user): `etcdStorage_open.law` (the bridge module's), the backend
constructor's pooled post split into the store's part (`mvccStorageFor`, at the image's data) and
the client's rest (`backendRest`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`etcdStorage_open.law`**: the image's receipt and facts, the store's part of the pooled post
(`isBackend` at the store's write invariant, the clean view, the deletable keys' and compaction
keys' parts, the safe-range slot, the counted readers), the registration and the payment rights
make `mvccStorageFor`; the rest is `backendRest`. -/
theorem etcdStorage_open.law_holds : etcdStorage_open.law (GF := GF) := by
  intro bk Pk K D L c u hP hcm
  iintro ⟨#Hsz, Himg, Hpost, Hreg, Hw1, Hw2, #Hsup, Hops⟩
  iunfold mvccImage at Himg
  icases Himg with ⟨#Hrc, %Himg⟩
  icases (backend.newPostKP_named bk.γB bk.P (fun _ => mvccW bk.gx) Pk K bk.be D) $$ Hpost with
    ⟨#HnB, #HnSC, HnK, HnV, HnH, HnRB, #HnPool, HnRT, HnDl, HnFk, HnSr⟩
  -- (the server's request, 2026-11-06) two of the counted slots' tokens for the client
  icases rep_sub _ 2 backend.rdStockN (by rw [backend.rdStockN_val]; omega) $$ HnRT
    with ⟨HnRT, Hrt2⟩
  simp only [List.replicate]
  icases BigSepL.bigSepL_cons.1 $$ Hrt2 with ⟨Hrt1, Hrt2⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrt2 with ⟨Hrt2, -⟩
  imodintro
  iframe Hrt1 Hrt2
  isplitr [HnSC HnK HnH HnRB HnPool]
  · iunfold mvccStorageFor
    iexists bk, D
    isplitr
    · ipureintro; exact ⟨rfl, hP, hcm, Himg⟩
    iunfold mvccW at HnB
    iunfold mvccWReg at Hreg
    iframe Hrc HnB Hsz HnV HnDl HnFk HnSr HnRT Hreg Hw1 Hw2 Hsup Hops
  · iunfold backendRest
    iframe HnSC HnK HnH HnRB HnPool

end laws

#print axioms etcdStorage_open.law_holds

end api
end mvcc
end EtcdGrove
end Perennial
