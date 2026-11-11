/-
`(*store).GetList(ctx, key, opts, listObj)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:763-860`):
a paginated list (no streaming: `rangeStreamOff`) of the prepared key's scope. The first page fires
`Q` (the state `σ` the read update fired at), the later pages `P σ` (reads at the first page's
revision, of one history with `σ`); the answer is the store's list `kListL` of `σ`'s store at the
read revision (`listRevL`: the latest, `σ`'s, or the past revision asked), in the list object
(`listIs`), or a too-large error when that revision is above `σ`'s, or a failed read's error
(`listErr`). `Q` fires for the revision `R'` its maker was given, `σ`'s on an answer; on a too-large
error `R'` may be any (7e-1's R1: from the client's error, the update was made for a revision the
client never learned). Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §2 with its corrections G1, G2, B2 and B5
(a)). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs

public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.GetList.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (L : ListSpec GF Obj)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (lx : GoInterface)
    (rv0 : w64) (cont0 : GoString) (rem0 : Option w64)
    (k : GoString) (n : w64) (sel : Obj → Bool) (emp : Bool)
    (Q : w64 → KVState → IProp GF) (P : KVState → KVState → IProp GF),
  (∀ R σ, Q R σ ⊢ ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ R σ σ', Q R σ ∗ P σ σ' ⊢ ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ⌜prepareKeyM c.resourcePrefix key opts.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV opts.ResourceVersion' = some n ∧
        opts.ResourceVersionMatch' ∈ [[], go!"NotOlderThan", go!"Exact"] ∧
        opts.Predicate'.Continue' = [] ∧ uint.Z n < 2 ^ 63 ∧
        0 ≤ sint.Z opts.Predicate'.Limit'⌝ ∗
      selPredOk c.S opts.Predicate' sel emp ∗ listContractOk c L ∗ rangeStreamOff ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ k8sctx.k8sCtxOk ci ∗ ctxNeverDone (GoInterface.ok ci) ∗ threadTok ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      L.listAt lx [] rv0 cont0 rem0 ∗
      (∀ R, |==> □ [∧list] x ∈ c.ms, ⌜Q R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R)) ∗
      (□ ∀ R σ, □ Q R σ -∗
        |==> □ [∧list] x ∈ c.ms, ⌜P σ = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (P σ)) }}
    (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"GetList")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #opts)) (Val #lx))
  {{ (err : GoInterface), RET #err; threadTok ∗
      ((listErr c err ∗ ∃ os rv cont rem, L.listAt lx os rv cont rem) ∨
       (∃ (R' : w64) (σ : KVState), □ Q R' σ ∗ ⌜σ.rev < uint.nat n ∨ R' = W64 (σ.rev : Int)⌝ ∗
         let R := listRevL opts.ResourceVersionMatch' opts.Recursive' opts.Predicate'.Limit' n
         if uint.Z R = 0 then
           -- a read at the latest revision, `σ`'s
           (if σ.rev < uint.nat n then
              iprop(apierrors.tooLargeErrIs err ∗ ∃ os rv cont rem, L.listAt lx os rv cont rem)
            else iprop(⌜err = GoInterface.nil⌝ ∗ listIs c L (c.pathPrefix ++ k) emp opts.Predicate'.Limit'
              (W64 (σ.rev : Int))
              (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k) opts.Recursive'
                σ.store) lx))
         else
           -- a read at the past revision `R`
           (if σ.rev < uint.nat R then
              iprop(apierrors.tooLargeErrIs err ∗ ∃ os rv cont rem, L.listAt lx os rv cont rem)
            else iprop(⌜err = GoInterface.nil⌝ ∗ listIs c L (c.pathPrefix ++ k) emp opts.Predicate'.Limit' R
              (kListL c.S.dec sel (limN opts.Predicate'.Limit') (c.pathPrefix ++ k) opts.Recursive'
                (σ.at (uint.nat R))) lx)))) }}

end spec

end k8s
end EtcdGrove
end Perennial
