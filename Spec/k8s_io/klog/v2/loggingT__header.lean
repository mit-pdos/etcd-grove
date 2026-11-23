/-
`(*loggingT).header(s, depth)` of klog's global `logging`: a fresh `*buffer.Buffer` holding some
bytes, the last not a newline, which the caller owns, with some file and line. Its code is the
trusted model `loggingT.header.impl` (`TrustedCode/k8s_io/klog/v2.lean`, which says why it is
faithful to Go's: the header's last two bytes, `"] "`, as Go's); proved over it
(`Proof/k8s_io/klog/v2/loggingT__header.lean`), from klog's fact (`klogInit`: `skipHeaders` false).
klog-printf, 2026-11-23, etcd-grove#25. Lean-first.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.bytes.BufferBasics

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
abbrev klog.loggingT.header.spec : Prop :=
  ∀ (s : w32) (depth : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }}
    (App (App (Val (globalAddr k8s_io.klog.v2.logging @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty
      @!! go!"header")) (Val #s)) (Val #depth))
  {{ (b : Loc) (file : GoString) (line : w64), RET (PairV (PairV #b #file) #line);
      ∃ bs : List w8, ⌜bs ≠ [] ∧ bs.getLast? ≠ some (W8 10)⌝ ∗
        _root_.Perennial.bytes.ownBuffer
          (structFieldRef k8s_io.klog.v2.internal.buffer.Buffer go!"Buffer" b) bs }}

end spec

end EtcdGrove
end Perennial
