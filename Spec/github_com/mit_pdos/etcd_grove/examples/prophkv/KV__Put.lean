/- Lean-first (no Rocq counterpart).

`kv.Put(k, v)` (`examples/prophkv`): the caller's ghost step runs at the linearization point (inside
the lock), from the abstract state `m` to `<[k := v]> m`, producing `R`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.prophkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.prophkv

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- See the file header. -/
abbrev KV__Put.spec : Prop :=
  ∀ (kv : Loc) (γ : GName) (k v : GoString) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.prophkv ∗
      isKV kv γ ∗ (∀ m, kvState γ m ={⊤}=∗ kvState γ (<[k := v]> m) ∗ R) }}
    (App (App (Val (kv @!! go.GoType.PointerType KV.ty @!! go!"Put")) (Val #k)) (Val #v))
  {{ RET #(); R }}

end spec

end prophkv
end EtcdGrove
end Perennial
