/- Lean-first (no Rocq counterpart).

`(*KV).Get(key)` (kv.go), logically atomic:
`<<∀ m, kvVal γr m>> Get key <<kvVal γr m, RET m key>>`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.Get.spec : Prop :=
  ∀ (γr : KVNames) (γp : RepNames) (r : Loc) (key : List w8) (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ isKV γr γp r ∗
      AU <{ ∃∃ (x : KVMap), kvVal γr x }> @ kvMask, ∅ <{ kvVal γr x, COMM Φ (x key) }> }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"Get")) (Val #key))
  {{ (v : List w8), RET #v; Φ v }}

end spec

end kv
end EtcdGrove
end Perennial
