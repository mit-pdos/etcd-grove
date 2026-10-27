/-
The reflector (`tools/cache/reflector.go`): what its specs are stated with. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (fourth round).

* `reflOwn r v u`: the reflector's last synced version `v` (`lastSyncResourceVersion`) and its
  "unavailable" flag `u` (`isLastSyncResourceVersionUnavailable`), owned by the reflector's
  goroutine, with a slot of their mutex (`lastSyncResourceVersionMutex`, a `sync.RWMutex` whose
  resource is `True`: the fields themselves are the owner's). In `Main` the reflector's goroutine is
  the only one that reads or writes them (`LastSyncResourceVersion` is called by `watch` only; the
  shared informer's and controller's `LastSyncResourceVersion` are not reached), so the mutex
  protects nothing another thread could see; a spec for concurrent readers would put the fields in
  the mutex's resource instead.
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The reflector's last synced version and flag**, its goroutine's. -/
def reflOwn (r : Loc) (v : GoString) (u : Bool) : IProp GF :=
  iprop(r.[Reflector, go!"lastSyncResourceVersion"] ↦ v ∗
    r.[Reflector, go!"isLastSyncResourceVersionUnavailable"] ↦ u ∗
    sync.ownRWMutex (r.[Reflector, go!"lastSyncResourceVersionMutex"]) (fun _ => iprop(True)))

/-- **The version a (re)list asks for** (`relistResourceVersion`): `""` (a consistent read) after
an expired or too-large version, `"0"` (any) before the first list, else the last synced one. -/
def relistRV (v : GoString) (u : Bool) : GoString :=
  if u then go!"" else if v = go!"" then go!"0" else v

/-- **The version a re-watch asks for** (`rewatchResourceVersion`). -/
def rewatchRV (v : GoString) (u : Bool) : GoString := if u then go!"" else v

end defs

end cache
end EtcdGrove
end Perennial
