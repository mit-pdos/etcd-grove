/-
`store.waitForRev(ctx, rev)` (`cache/store.go`, new in etcd-io/etcd#21600). Lean-first (no Rocq
counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore
public import Spec.context.Err

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.waitForRev(ctx, rev)`, by a reader of the store (`storeReader`, given back): `nil` only once
the store's latest revision is at least `rev` (`storeRevLb`); else the context's non-nil error
once it is done, whose `Error()` returns some string (`context.errStringOk`). It waits on the
store's `revCond` under a read lock, with `context.AfterFunc(ctx, revCond.Broadcast)` to wake it
when the context is done. Partial correctness: the spec does not say that it returns (it may not:
the `Broadcast` can be lost, `issues/cache-waittillrevision-lost-wakeup.md`). -/
abbrev store.waitForRev.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF)
    (ctx : GoInterfaceOk) (cs : _root_.Perennial.context.ContextDesc (IProp GF)) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeReader s γ cap E R ∗ _root_.Perennial.context.isContext ctx cs }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"waitForRev"))
      (Val #(GoInterface.ok ctx))) (Val #rev))
  {{ (err : GoInterface), RET #err; storeReader s γ cap E R ∗
      ((⌜err = GoInterface.nil⌝ ∗ storeRevLb γ rev) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ □ cs.PDone ∗ _root_.Perennial.context.ContextClosed cs.Done_gn ∗
         context.errStringOk err)) }}

end spec

end EtcdGrove
end Perennial
