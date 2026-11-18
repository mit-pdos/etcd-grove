/-
`handleCompactedErrorForPaging(continueKey, keyPrefix)` (`k8s.io/apiserver/pkg/storage/etcd3/
errors.go:77-89`; k8s 7f-5a-P, E5): for a continue key the prefix encodes (`encOkL`, so
`storage.EncodeContinue` succeeds and the untranslated `utilruntime.HandleError` is not reached), a
`*StatusError` from `NewResourceExpired(inconsistentContinue)` whose `ListMeta.Continue` is set to the
new token: a 410 `Expired` `Failure` status, no details. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev handleCompactedErrorForPaging.spec : Prop :=
  ∀ (ck kp : GoString),
  k8s_etcd3.encOkL ck kp = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.handleCompactedErrorForPaging)) (Val #ck))
      (Val #kp))
  {{ (e : GoInterface), RET #e; ∃ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status,
      apierrors.apiErrAt e (.status st []) ∗
      ⌜st.Reason' = go!"Expired" ∧ st.Code' = W32 410 ∧ st.Status' = go!"Failure"⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
