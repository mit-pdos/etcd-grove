/-
`klog.infoSArgOk`: the keys and values klog's structured calls (`Verbose.InfoS`) are given, which
its serializer (`serialize.FormatKVs`, trusted: `TrustedCode/k8s_io/klog/v2/internal/serialize.lean`)
formats without calling foreign code or panicking. Moved here from `Verbose__InfoS.lean` (klog-infos,
2026-11-23), unchanged, for the serializer's spec. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A key or value `InfoS` is given by the watcher's block logger: a `string`, an `int`, a
`time.Duration` or a `schema.GroupResource`. -/
def klog.infoSArgOk (x : GoInterface) : Prop :=
  ∃ ii : GoInterfaceOk, x = GoInterface.ok ii ∧
    ii.ty ∈ [go.string, go.int, _root_.Perennial.time.Duration.ty,
      k8s_io.apimachinery.pkg.runtime.schema.GroupResource.ty]

end spec

end EtcdGrove
end Perennial
