/-
`storage.PrepareContinueToken(keyLastEvaluated, keyPrefix, rv, itemsCount, hasMore, opts)`
(`k8s.io/apiserver/pkg/storage/continue.go:100-122`): with no more items, no token and no count;
with more, `EncodeContinue(keyLastEvaluated + "\x00", keyPrefix, rv)` (`encL`, or its error where the
prefix is no non-empty prefix of the key, `encOkL`), and the remaining count `itemsCount - Limit`
iff the predicate is empty (`selPredOk`'s `Empty`). Proved from the translated body (stage 7e-2,
`notes/k8s-7e-2-draft.md` §4.2, the final generic form; it replaces 7e-3b's driver-specialized
hypothesis, #22). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.SelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI k8s k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.PrepareContinueToken.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (kl kp : GoString) (rv cnt : w64) (more : Bool)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (sel : Obj → Bool) (emp : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗
      selPredOk S opts.Predicate' sel emp }}
    (App (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.PrepareContinueToken))
      (Val #kl)) (Val #kp)) (Val #rv)) (Val #cnt)) (Val #more)) (Val #opts))
  {{ (t : GoString) (rem : Loc) (err : GoInterface), RET (PairV (PairV #t #rem) #err);
      if more then
        (if encOkL (kl ++ [W8 0]) kp then
          ⌜err = GoInterface.nil ∧ t = encL (kl ++ [W8 0]) kp rv⌝ ∗
            (if emp then rem ↦ (cnt - opts.Predicate'.Limit') else ⌜rem = null⌝)
        else ⌜err ≠ GoInterface.nil⌝)
      else ⌜t = [] ∧ rem = null ∧ err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
