/-
**`Compact`'s channel, made and received on** (mvccfull's Prove, 2026-11-10, the "minor spec fixes"
rule): `KV.Compact.contract`'s `compactChanOk` says only that a receive on the channel does not
panic, which a `nil` channel meets (its receive blocks) and whose result is any value. Etcd's
`store.Compact` returns a channel `make(chan struct{})` in both the success and the `ErrCompacted`
arm (`kvstore.go`, `compact` and `updateCompactRev`), and a receive on a `chan struct{}` returns the
pair of the element and `ok`. The tester checks `ch != nil` and takes `<-ch`'s first component.

`compactChanRecv` adds exactly those two facts (no ghost state), and `compactChan.law` gives
`KV.Compact.contract` with it in place of `compactChanOk` at every store handle (`isMvcc`). In a
module of its own, so that adding it leaves `Api` (and its importers) as they were.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- **A compaction's channel, made and received on**: not `nil`, and a receive on it does not
panic and returns the pair of `struct{}{}` and `ok` (`compactChanOk` with the two facts). -/
def compactChanRecv (ch : GoChan) : IProp GF :=
  iprop(⌜ch ≠ chan.nil⌝ ∗ □ {{ True }} (App (Val (chan.receive (go.GoType.StructType []))) (Val #ch))
    {{ (ok : Bool), RET (PairV #() #ok); True }})

instance compactChanRecv_persistent (ch : GoChan) : Persistent (compactChanRecv (GF := GF) ch) := by
  unfold compactChanRecv; infer_instance

/-- **`Compact(trace, rev)`, with its channel made** (`KV.Compact.contract`, `compactChanRecv` in
place of `compactChanOk`). -/
abbrev KV.Compact.contractC (ty : go.GoType) (v : val) : Prop :=
  ∀ (γ : MvccName) (trace : Loc) (te : Bool) (rev : w64) (q : Qp) (B : MvccStorage)
    (P : IProp GF) (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Q : MvccState → IProp GF),
  {{ pkgInit ∗ isMvcc (interface.mkOk ty v) γ ∗ mvccOpen γ ∗ ⌜trace ≠ null⌝ ∗
      ⌜1 ≤ sint.Z rev⌝ ∗
      traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗ hookIs B f ∗
      X ∗ storageReq B P X Y ∗
      Pre ∗ hookRun P f Pre Q' ∗ (Q' ={⊤}=∗ P ∗ Post) ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ (if σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)
              then σ.compactTo (sint.Z rev) else σ), COMM Q σ }> }}
    (App (App (Val #(methods ty go!"Compact" v)) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      mvccOpen γ ∗ traceutil.ownTrace trace te ∗ mvccBackend γ q B P ∗
      ∃ σ : MvccState, Q σ ∗
      ((⌜err = GoInterface.nil ∧ σ.crev < sint.Z rev ∧ sint.Z rev ≤ (σ.rev : Int)⌝ ∗ Post ∗ Y ∗
          compactChanRecv ch) ∨
       (⌜sint.Z rev ≤ σ.crev⌝ ∗ globalAddr ErrCompacted ↦□ err ∗ Pre ∗ X ∗ compactChanRecv ch) ∨
       (⌜(σ.rev : Int) < sint.Z rev ∧ ch = chan.nil⌝ ∗ globalAddr ErrFutureRev ↦□ err ∗ Pre ∗ X)) }}

/-- **A store handle's `Compact` makes its channel**: at every handle `isMvcc`, the method meets
`KV.Compact.contractC`. -/
abbrev compactChan.law : Prop :=
  ∀ (ty : go.GoType) (v : val) (γ : MvccName),
    isMvcc (GF := GF) (interface.mkOk ty v) γ ⊢ ⌜KV.Compact.contractC (GF := GF) ty v⌝

end laws

end api
end mvcc
end EtcdGrove
end Perennial
