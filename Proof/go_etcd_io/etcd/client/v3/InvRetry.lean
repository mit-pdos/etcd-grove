/-
**The client's retry interceptor** (unit P3a, 2026-10-14): the vocabulary of the proofs of
`retry_interceptor.go`'s `unaryClientInterceptor` and its helpers (`retry.go`'s
`isSafeRetry*`), below the contract the interceptor meets (`etcdInterceptorOk`,
`InvKVConn.lean`). Lean-first (no Rocq counterpart); the design: `notes/decisions.md`, "The retry
interceptor proved: the gRPC boundary below it".

**The options** (`*options`: `retryPolicy`, `max`, `backoffFunc`, `retryAuth`): read-only once
built (`retryOptsAt o`), their backoff function one that returns (`optionsOk`, `backoffOk`:
`waitRetryBackoff`, an axiom, calls it). The interceptor's own options are built at
`unaryClientInterceptor` from `defaultOptions` (a package fact) by the dial's `retryOption`s
(`optApplyOk`: any write of the options keeping `optionsOk`: `withMax`'s, `withBackoff`'s); a
call's by the call's `retryOption`s (`retryApplyOk`, `InvKVConn.lean`: they write only
`retryPolicy`).

**The client** (`retryClientOk c`): what the interceptor reads of the `*Client` `c`: its logger
(`isClientLogger`), its `Token` and `authTokenBundle` (fixed since `clientv3.New`, which sets the
bundle whenever it sets a token: an assumption about the unverified constructor, as
`clientKVAt`'s), and what the axiomatized `getToken` (the auth client) and `Endpoints` (a read under
`epMu`) need of it.

**Errors** (`clientErrOk err`): `nil`, or a client error (`clientErr`) grpc's `status` accepts
(`statusErrOk`): what every error the interceptor sees or returns is.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvClient

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **An error the client's retry path handles** (persistent): `nil`, or a client error
(`clientErr`) that grpc's `status` accepts (`statusErrOk`). -/
def clientErrOk (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil → clientErr err⌝ ∗ statusErrOk err)

instance clientErrOk_persistent (err : GoInterface) : Persistent (clientErrOk (GF := GF) err) := by
  unfold clientErrOk; infer_instance

theorem clientErrOk_nil : ⊢ clientErrOk (GF := GF) GoInterface.nil := by
  unfold clientErrOk
  isplitl
  · ipureintro; intro h; exact absurd rfl h
  · iapply statusErrOk_nil

/-- **The interceptor's options value** `ov`: its backoff function returns. -/
def optionsOk (ov : go_etcd_io.etcd.client.v3.options) : IProp GF := backoffOk ov.backoffFunc'

instance optionsOk_persistent (ov : go_etcd_io.etcd.client.v3.options) :
    Persistent (optionsOk (GF := GF) ov) := by
  unfold optionsOk; infer_instance

/-- **The `*options` `o`, read-only** (persistent), with `optionsOk`. -/
def retryOptsAt (o : Loc) : IProp GF :=
  iprop(∃ ov : go_etcd_io.etcd.client.v3.options, o ↦□ ov ∗ optionsOk ov)

instance retryOptsAt_persistent (o : Loc) : Persistent (retryOptsAt (GF := GF) o) := by
  unfold retryOptsAt; infer_instance

/-- **A `retryOption`'s closure `f` building options** (persistent): it writes the options it is
given, keeping `optionsOk` (the dial's `withMax`, `withBackoff`; a call's `retryApplyOk`). -/
def optApplyOk (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (o : Loc) (ov : go_etcd_io.etcd.client.v3.options),
    {{ o ↦ ov ∗ optionsOk ov }}
      (App (Val #f) (Val #o))
    {{ RET #(); ∃ ov' : go_etcd_io.etcd.client.v3.options, o ↦ ov' ∗ optionsOk ov' }})

instance optApplyOk_persistent (f : GoFunc) : Persistent (optApplyOk (GF := GF) f) := by
  unfold optApplyOk; infer_instance

/-- The options' fields, split from the struct (`bb_fields_acc`'s idiom). -/
theorem options_fields_acc (l : Loc) (v : go_etcd_io.etcd.client.v3.options) :
    (l ↦ v : IProp GF) ⊢
      structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" l ↦ v.retryPolicy' ∗
      (∀ p : go_etcd_io.etcd.client.v3.retryPolicy,
        structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" l ↦ p -∗
        l ↦ { v with retryPolicy' := p }) := by
  iintro H
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
  iStructNamed H
  iframe retryPolicy
  iintro %p Hp
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-- The fields of read-only options, read-only. -/
theorem options_fields_ro (l : Loc) (v : go_etcd_io.etcd.client.v3.options) :
    (l ↦□ v : IProp GF) ⊢
      structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" l ↦□ v.retryPolicy' ∗
      structFieldRef go_etcd_io.etcd.client.v3.options go!"max" l ↦□ v.max' ∗
      structFieldRef go_etcd_io.etcd.client.v3.options go!"backoffFunc" l ↦□ v.backoffFunc' ∗
      structFieldRef go_etcd_io.etcd.client.v3.options go!"retryAuth" l ↦□ v.retryAuth' := by
  iintro #H
  iStructNamed H
  iframe #

/-- A call's `retryOption` (`retryApplyOk`: it writes only `retryPolicy`) builds options. -/
theorem optApplyOk_of_retryApplyOk (f : GoFunc) :
    retryApplyOk (GF := GF) f ⊢ optApplyOk f := by
  iintro #Hf
  unfold optApplyOk
  iintro !> %o %ov %Φ !> ⟨Ho, #Hok⟩ HΦ
  icases options_fields_acc o ov $$ Ho with ⟨Hp, Hback⟩
  unfold retryApplyOk
  wp_apply Hf $$ [Hp] as Hp
  · iframe
  icases Hp with ⟨%p', Hp⟩
  iapply HΦ
  iexists { ov with retryPolicy' := p' }
  isplitl [Hback Hp]
  · iapply Hback $$ Hp
  · unfold optionsOk at *
    iexact Hok

/-- **What the retry interceptor reads of the `*Client` `c`** (persistent; see the file header):
non-nil, its logger, its `Token` and `authTokenBundle` (read-only; a bundle whenever a token). -/
def retryClientOk (c : Loc) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ isClientLogger c ∗
    ∃ (tok : GoString) (atb : GoInterface),
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c ↦□ tok ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"authTokenBundle" c ↦□ atb ∗
      ⌜tok ≠ go!"" → atb ≠ GoInterface.nil⌝)

instance retryClientOk_persistent (c : Loc) : Persistent (retryClientOk (GF := GF) c) := by
  unfold retryClientOk; infer_instance

end defs

end EtcdGrove
end Perennial
