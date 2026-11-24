/-
`serialize.FormatKVs(b, kvs...)` (klog v2.140.0, `internal/serialize/keyvalues.go:64`): appends the
key/value pairs of the slices `kvs` to the `bytes.Buffer` `b`. Trusted: a model
(`TrustedCode/k8s_io/klog/v2/internal/serialize.lean`, klog-infos, 2026-11-23, etcd-grove#25) that
reads every key and value, is stuck unless each is `klog.infoSArgOk`, and appends arbitrary bytes;
proved over the model (`Proof/k8s_io/klog/v2/internal/serialize/FormatKVs.lean`). Here: the
buffer, holding `bs`, comes back holding `bs` and some more bytes; the slices, read at any
fraction, come back. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.klog.v2.KVArgs

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

/-- See the file header. -/
abbrev klog.serialize.FormatKVs.spec : Prop :=
  ∀ (b : Loc) (bs : List w8) (kvs : GoSlice) (sls : List GoSlice) (xss : List (List GoInterface))
    (dq dq' : DFrac),
  (∀ xs ∈ xss, ∀ x ∈ xs, klog.infoSArgOk x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2.internal.serialize ∗
      _root_.Perennial.bytes.ownBuffer b bs ∗ kvs ↦*{dq'} sls ∗
      [∗list] sl;xs ∈ sls;xss, sl ↦*{dq} xs }}
    (App (App (Val (@! k8s_io.klog.v2.internal.serialize.FormatKVs)) (Val #b)) (Val #kvs))
  {{ RET #(); (∃ q : List w8, _root_.Perennial.bytes.ownBuffer b (bs ++ q)) ∗ kvs ↦*{dq'} sls ∗
      [∗list] sl;xs ∈ sls;xss, sl ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
