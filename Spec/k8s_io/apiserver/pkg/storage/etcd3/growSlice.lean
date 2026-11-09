/-
`growSlice(v, maxCapacity, sizes...)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:1117-1140`) on
the items slice of a list: the items unchanged, possibly in a new slice of a larger capacity
(`Cap`, `Len`, `MakeSlice`, `Copy`, `Set`; `listContractOk'`'s clauses at the store's element
type). `sint.Z mx ≤ 2 ^ 41` (revision after the attack): the capacity asked of `MakeSlice` is at
most `mx`. The variadic `sizes` slice is a parameter. Proved (stage 7e-2,
`notes/k8s-7e-2-draft.md` §3.3). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver reflectM

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev growSlice.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (L : ListSpec GF Obj) (vp : Loc)
    (v : _root_.Perennial.reflect.Value) (p : Loc) (s : GoSlice) (os : List (Obj × GoString))
    (mx : w64) (szs : GoSlice) (zs : List w64),
  sint.Z mx ≤ 2 ^ 41 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      listContractOk' S L ∗ ⌜reflElem v (go.GoType.SliceType S.objTy) p⌝ ∗
      p ↦ s ∗ L.itemsAt s os ∗ szs ↦*□ zs }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.growSlice)) (Val #v)) (Val #mx))
      (Val #szs))
  {{ RET #(); ∃ s', p ↦ s' ∗ L.itemsAt s' os }}

end spec

end k8s
end EtcdGrove
end Perennial
