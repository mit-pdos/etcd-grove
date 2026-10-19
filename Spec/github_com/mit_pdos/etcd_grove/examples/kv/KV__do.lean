/- Lean-first (no Rocq counterpart).

`(*KV).do(kind, key, val)` (kv.go): one operation, logically atomic: the client's atomic update
over the store's state takes effect when the operation's first entry is committed
(`kv_propAu`), moving the state by `kvNext kind key val`; `do` returns the key's value after
it. (Until 2026-10-19 an operation credit too: a replica out of sequence numbers now stops in
Go.)
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
abbrev KV.do.spec : Prop :=
  ∀ (γr : KVNames) (γp : RepNames) (r : Loc) (kind : w8) (key val : List w8)
    (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 62 → (val.length : Int) < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ isKV γr γp r ∗
      AU <{ ∃∃ (x : KVMap), kvVal γr x }> @ kvMask, ∅
        <{ kvVal γr (kvNext kind key val x), COMM Φ (kvNext kind key val x key) }> }}
    (App (App (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"do")) (Val #kind)) (Val #key))
      (Val #val))
  {{ (res : List w8), RET #res; Φ res }}

end spec

end kv
end EtcdGrove
end Perennial
