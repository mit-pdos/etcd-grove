/- Lean-first (no Rocq counterpart).

`(*KV).Append(key, val)` (kv.go), logically atomic:
`<<∀ m, rkvVal γr m>> Append key val <<rkvVal γr (m[key := m key ++ val])>>`.
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
abbrev KV.Append.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (key val : List w8) (Φ : IProp GF),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ isKV γr γp r ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvMask, ∅
        <{ rkvVal γr (kvUpd x key (x key ++ val)), COMM Φ }> }}
    (App (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"Append")) (Val #key)) (Val #val))
  {{ RET #(); Φ }}

end spec

end kv
end EtcdGrove
end Perennial
