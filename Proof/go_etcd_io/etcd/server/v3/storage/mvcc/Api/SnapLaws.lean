/-
**The snapshot image's laws of mvcc's API** (stage 2, M2, 2026-11-05: `notes/mvcc-api-risk.md`,
M2), over the sealed definitions (`Api.lean`: `mvccImage`, its pure part `snap.imageOk`,
`Api/SnapImage.lean`). Lean-first (no Rocq counterpart).
- `mvccImage_persistent` (the image's conjunct of `persistent.law`);
- `mvccImage_fresh.law_holds`: a fresh backend's data is the empty history's image, its receipt
  `⧖ 0` allocated (`preceipt_zero`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage

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

instance mvccImage_persistent (D : backend.Data) (L : Log) (c : Int) (u : Bool) :
    Persistent (mvccImage (GF := GF) D L c u) := by
  unfold mvccImage; infer_instance

/-- **`mvccImage_fresh.law`**: no change, so the receipt `⧖ 0`; the facts `snap.imageOk_fresh`. -/
theorem mvccImage_fresh.law_holds : mvccImage_fresh.law (GF := GF) := by
  intro D hk hs hf
  iintro
  imod preceipt_zero (GF := GF) with #H0
  imodintro
  unfold mvccImage
  isplitl
  · rw [show logCh mvccStart.log = 0 from rfl]
    iexact H0
  · ipureintro; exact snap.imageOk_fresh D hk hs hf

end laws

#print axioms mvccImage_fresh.law_holds

end api
end mvcc
end EtcdGrove
end Perennial
