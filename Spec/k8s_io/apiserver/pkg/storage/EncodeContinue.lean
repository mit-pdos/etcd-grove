/-
`storage.EncodeContinue(key, keyPrefix, rv)` (`k8s.io/apiserver/pkg/storage/continue.go:83-98`):
where the prefix is a non-empty prefix of the key (`encOkL`), the token `encL key keyPrefix rv` (the
base64 URL encoding without padding of the JSON of `{"v": "meta.k8s.io/v1", "rv": rv, "start": key
without prefix}`) and no error; else an error. Proved from the translated body, `strings.TrimPrefix`
(Perennial), `json.Marshal`'s and `RawURLEncoding`'s trusted specs (stage 7e-2,
`notes/k8s-7e-2-draft.md` §4.2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI k8s_etcd3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.EncodeContinue.spec : Prop :=
  ∀ (key kp : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.EncodeContinue)) (Val #key)) (Val #kp))
      (Val #rv))
  {{ (t : GoString) (err : GoInterface), RET (PairV #t #err);
      ⌜if encOkL key kp then t = encL key kp rv ∧ err = GoInterface.nil
       else err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
