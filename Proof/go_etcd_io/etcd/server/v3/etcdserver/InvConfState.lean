/-
The backend's conf state, read at bootstrap (`schema.ReadConfStateFromBackend`, added by
etcd-io/etcd#19693; pr-verify, 2026-10-17). Lean-first (no Rocq counterpart).

`csReadTx rt` is the contract of a `ReadTx` the conf state is read through: `RLock`/`RUnlock`
return, and its `UnsafeRange` on the conf-state key (bucket `Meta`, key `"confState"`, no end, no
limit) returns. What the stored bytes are is not modelled: `UnsafeConfStateFromBackend`
(names-only: it decodes them with `encoding/json`'s `Unmarshal`) is the trust boundary, as
`MustUnsafeSaveConfStateToBackend`, which encodes them, is (`InvHooks.lean`). `csRead cs` is what
it returns: `nil` (nothing stored: a backend written before v3.5) or a fresh conf state, owned.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvHooks
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `UnsafeRange` of the reader `r` on the conf-state key returns (some slices). -/
def csRangeOk (r : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ (b : GoInterface) (key : GoSlice),
    {{ globalAddr schema.Meta ↦□ b ∗ key ↦*□ schema.confStateKeyBytes }}
      (App (App (App (App (Val #(methods r.ty go!"UnsafeRange" r.v)) (Val #b)) (Val #key))
        (Val #(slice.nil))) (Val #(W64 0)))
    {{ (ks vs : GoSlice), RET (PairV #ks #vs); True }}))

/-- A `ReadTx` the conf state is read through: its read lock, and `csRangeOk`. -/
def csReadTx (rt : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #())) {{ RET #(); True }}) ∗
    csRangeOk rt)

instance csReadTx_persistent (rt : GoInterfaceOk) : Persistent (csReadTx (GF := GF) rt) := by
  unfold csReadTx csRangeOk; infer_instance

/-- What the conf state's read returns: `nil`, or a fresh conf state, owned. -/
def csRead (cs : Loc) : IProp GF :=
  iprop(⌜cs = null⌝ ∨ ∃ c : ConfStateM, ownCSM cs (DFrac.own 1) c)

end defs

end EtcdGrove
end Perennial
