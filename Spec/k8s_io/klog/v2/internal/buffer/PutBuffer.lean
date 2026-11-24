/-
`buffer.PutBuffer(b)` (klog v2.140.0, `internal/buffer/buffer.go:59-72`): gives the buffer, owned
whole, back to the pool (unless it holds 256 bytes or more: then dropped). Proved over its
translated body and Perennial's `sync.Pool` (`Proof/k8s_io/klog/v2/internal/buffer/PutBuffer.lean`;
klog-infos, 2026-11-23, etcd-grove#25). Lean-first (no Rocq counterpart).
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

/-- See the file header. -/
abbrev klog.buffer.PutBuffer.spec : Prop :=
  ∀ (b : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2.internal.buffer ∗
      k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer b bs }}
    (App (Val (@! k8s_io.klog.v2.internal.buffer.PutBuffer)) (Val #b))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
