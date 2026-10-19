/- Lean-first (no Rocq counterpart).

`(*KV).Read(key)` (kv.go), a linearizable read of a key by read index (2026-10-13): for a
lower bound `L0` on the store's history at the call (`kvLb`, `Defs.lean`; the history now is
one, `kvLb_current`), it returns the key's value after a history `L` that extends `L0` and is
itself a lower bound, so a prefix of the history at the return: the key's value at a point
between the call and the return. Not logically atomic: which history the value is of is known
only after the fact (when the read state comes back, its read index is in the past), so the
spec is stated with lower bounds, as raft's `ReadState` is (`readOk`).

One read credit (`rdCred`, what `Node.ReadIndex` takes); any number of voters. A request raft
drops (no leader known) leaves `Read` waiting: partial correctness. (Until 2026-10-19 an
operation credit too.)
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
abbrev KV.Read.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (key : List w8) (L0 : List (List w8)),
  (key.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isKV γr γp r ∗ rdCred γr.raft 1 ∗ kvLb γr L0 }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"Read")) (Val #key))
  {{ (x : List w8), RET #x; ∃ L, kvLb γr L ∗ ⌜L0 <+: L ∧ x = kvFold L key⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
