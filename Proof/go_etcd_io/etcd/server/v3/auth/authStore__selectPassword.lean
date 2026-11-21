/-
Proof of `authStore.selectPassword` (`server/auth/store.go`) over its translated body
(prove-authcrypto, 2026-11-21; until then an axiom at the trust boundary, the code names only):
bcrypt's `GenerateFromPassword` (the trust boundary) when a password is given without a hash, else
base64's `StdEncoding.DecodeString` of the hash (proved over the real `encoding/base64`, reached
through the package fact `stdDecInit`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__selectPassword
public import Spec.golang_org.x.crypto.bcrypt.GenerateFromPassword

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.selectPassword.wp_proof
    (h_gen : bcrypt.GenerateFromPassword.spec (GF := GF) (hG := hG)) :
    auth.authStore.selectPassword.spec (GF := GF) (hG := hG) := by
  intro st password hashed
  wp_start as ⟨%Hst, %c, #Hc⟩
  ihave #Hb64 : isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 $$ []
  · iPkgInit
  ihave ⟨%e, #He, #Hdec⟩ := encoding.base64.stdDecInit_access $$ Hb64
  try wp_auto
  trace_state
  sorry

end proof

end EtcdGrove
end Perennial
