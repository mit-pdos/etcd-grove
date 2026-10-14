/-
`recipes.(*RWMutex).waitOnLastRev(pfx)` (`client/v3/experimental/recipes/rwmutex.go`). Lean-first (no Rocq counterpart);
see `InvRWMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRWMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`rwm.waitOnLastRev(bp)`**, with the key `st` (created at `st.rev > 0`) in `myKey`, for a
prefix `bp` under the mutex's `pfx`, knowing etcd has reached `lo`: the get
`Get(bp, WithLastRev()..., WithMaxModRev(st.rev - 1))` (the key with the prefix `bp` with the
greatest mod revision below `st.rev`); `(true, nil)` if there is none: at the get's revision
`R ≥ lo`, no key with the prefix `bp` has a mod revision below `st.rev` (`RWBlockFree`); otherwise
`WaitEvents` for that key's deletion from `st.rev` on, and `false` (with its error, always `nil`,
or the get's error). The key is unchanged. -/
abbrev RWMutex.waitOnLastRev.spec : Prop :=
  ∀ (m s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (pfx bp : GoString)
    (ek : Loc) (st : RemoteKVSt) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRWMutex m s γ client id pfx ∗ rwMyKey m pfx (some (ek, st)) ∗ etcdReached lo ∗
      ⌜pfx <+: bp ∧ 0 < sint.Z st.rev⌝ }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"waitOnLastRev")) (Val #bp))
  {{ (done : Bool) (err : GoInterface), RET (PairV #done #err); rwMyKey m pfx (some (ek, st)) ∗
      ((⌜done = true ∧ err = GoInterface.nil⌝ ∗ ∃ (R : w64) (s' : List EtcdKv), etcdReached R ∗
          □ etcdState R pfx s' ∗ ⌜sint.Z lo ≤ sint.Z R ∧ RWBlockFree bp st.rev s'⌝) ∨
        ⌜done = false⌝) }}

end spec

end recipes
end EtcdGrove
end Perennial
