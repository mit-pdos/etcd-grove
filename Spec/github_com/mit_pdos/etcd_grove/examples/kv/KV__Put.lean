/- Lean-first (no Rocq counterpart).

`(*KV).Put(key, val)` (kv.go), logically atomic:
`<<∀ m, kvVal γr m>> Put key val <<kvVal γr (m[key := val])>>`, in Iris's form: the client's
atomic update (at `kvMask`: not raft's commit invariant nor the store's).
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
abbrev KV.Put.spec : Prop :=
  ∀ (γr : KVNames) (γp : RepNames) (r : Loc) (key val : List w8) (Φ : IProp GF),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ isKV γr γp r ∗
      AU <{ ∃∃ (x : KVMap), kvVal γr x }> @ kvMask, ∅ <{ kvVal γr (kvUpd x key val), COMM Φ }> }}
    (App (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"Put")) (Val #key)) (Val #val))
  {{ RET #(); Φ }}

end spec

end kv
end EtcdGrove
end Perennial
