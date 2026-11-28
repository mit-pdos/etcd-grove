/- Lean-first (no Rocq counterpart).

`decodeItemRVs(s)` (export.go, notes/k8s-dist-k9.md §2.5): `decItemRVsL` (`SharedLand.lean`): the
items `s` encodes, each keyed by its object's `Namespace/Name` (`objKeyL`), or false. The slice is
fresh (owned).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj item)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev decodeItemRVs.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeItemRVs)) (Val #s))
  {{ (sl : GoSlice) (ok : Bool), RET (PairV #sl #ok);
      match decItemRVsL s with
      | some os => ⌜ok = true⌝ ∗ sl ↦* os.map (fun o => item.mk (objKeyL o) o false)
      | none => ⌜ok = false⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
