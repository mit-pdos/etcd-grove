/-
`bytealg.LastIndexByteString` (`lastindexbyte_generic.go`; rafthttp stage 5d, `path.Split` and
`path.Base`). Lean-first; the model: `Proof/path/Model.lean`.
-/
module

public import Proof.path.Model
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `LastIndexByteString(s, c)`: the last index of `c` in `s`, or `-1` (`path.lastIndexByte`). -/
abbrev bytealg.LastIndexByteString.spec : Prop :=
  ∀ (s : GoString) (c : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
    (App (App (Val (@! _root_.Perennial.internal.bytealg.LastIndexByteString)) (Val #s)) (Val #c))
  {{ RET #(W64 (path.lastIndexByte s c)); ⌜s.length < 2 ^ 63⌝ }}

end spec

end EtcdGrove
end Perennial
