/-
**The stopped view's laws for clients** (mvccfull's Probe, 2026-11-09, the unfold list): what a
client of `Close` used to get by unfolding `bStopView` and `rbOwn`. In a module of its own, so that
adding it leaves the backend's other modules (and their importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section stop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A part of the tracked buckets agrees with the stopped view**: `Close`'s data `D` holds, at
each bucket of `S`, what the part `rbPart γ S r` says the writer's contents hold. -/
theorem bStopView_rbPart_agree (γ : BNames) (P : BParams) (W Pk : IProp GF) (D : Data)
    (S : GoString → Prop) (r : GMap GoString BktData) :
    bStopView γ P W Pk D ∗ rbPart γ S r ⊢
      bStopView γ P W Pk D ∗ rbPart γ S r ∗ ⌜∀ n, S n → r.lookup n = (rbData P D).lookup n⌝ := by
  unfold bStopView rbOwn
  iintro ⟨⟨HW, HPk, HX, Hhk, Hown, Hfkd, Hfk⟩, Hrb⟩
  icases rbPart_agree γ S (fun _ => True) r _ $$ [$Hrb $Hown] with ⟨Hrb, Hown, %Ha⟩
  iframe HW HPk HX Hhk Hown Hfkd Hfk Hrb
  ipureintro
  intro n hn
  exact Ha n hn trivial

end stop

end backend
end EtcdGrove
end Perennial
