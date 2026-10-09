/-
`store.getSnapshot(rev)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.getSnapshot(rev)` (under a read lock): for some state `st` of the store (at least the
caller's lower bound `r0`, `storeSeen`), what `snapModel st rev` says: the snapshot (a
read-only `*snapshot`, `snapIs`, with its certificate: `snapCert`) and `st`'s latest revision, or `nil`, `0` and the error
(`snapErr`). -/
abbrev store.getSnapshot.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (r0 : w64) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeReader s γ cap E ∗ storeRevLb γ r0 }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"getSnapshot")) (Val #rev))
  {{ (p : Loc) (lrev : w64) (err : GoInterface), RET (PairV (PairV #p #lrev) #err);
      storeReader s γ cap E ∗
      ∃ st : StoreState, storeSeen γ cap r0 st ∗ snapErr (snapModel st rev) err ∗
        match snapModel st rev with
        | .ok r m => ⌜lrev = st.latestRev⌝ ∗ snapCert E p (r, m)
        | _ => ⌜p = null ∧ lrev = W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
