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

/-- **A `retryOption`'s closure `f`, keeping the retry policy** (persistent; 2026-10-21, D29): as
`optApplyOk`, and with `kp`, the retry policy kept (the dial's `withMax`, `withBackoff`; not a
call's, which may set it). -/
def optApplyKeep (f : GoFunc) (kp : Bool := false) : IProp GF :=
  iprop(□ ∀ (o : Loc) (ov : go_etcd_io.etcd.client.v3.options),
    {{ o ↦ ov ∗ optionsOk ov }}
      (App (Val #f) (Val #o))
    {{ RET #(); ∃ ov' : go_etcd_io.etcd.client.v3.options, o ↦ ov' ∗ optionsOk ov' ∗
        ⌜kp = true → ov'.retryPolicy' = ov.retryPolicy'⌝ }})

instance optApplyKeep_persistent (f : GoFunc) (kp : Bool) :
    Persistent (optApplyKeep (GF := GF) f kp) := by
  unfold optApplyKeep; infer_instance

/-- **The read-only options `o` with the retry policy `p`** (persistent; D29). -/
def retryOptsPol (o : Loc) (p : go_etcd_io.etcd.client.v3.retryPolicy) : IProp GF :=
  iprop(∃ ov : go_etcd_io.etcd.client.v3.options, o ↦□ ov ∗ ⌜ov.retryPolicy' = p⌝)

instance retryOptsPol_persistent (o : Loc) (p : go_etcd_io.etcd.client.v3.retryPolicy) :
    Persistent (retryOptsPol (GF := GF) o p) := by
  unfold retryOptsPol; infer_instance

theorem optApplyKeep_ok (f : GoFunc) (kp : Bool) :
    optApplyKeep (GF := GF) f kp ⊢ optApplyOk f := by
  iintro #Hf
  unfold optApplyOk
  iintro !> %o %ov %Φ !> Hpre HΦ
  unfold optApplyKeep
  wp_apply Hf $$ Hpre as Hres
  icases Hres with ⟨%ov', Ho, #Hok, -⟩
  iapply HΦ
  iexists ov'
  iframe Ho Hok

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
theorem optApplyKeep_of_retryApplyOk (f : GoFunc) :
    retryApplyOk (GF := GF) f ⊢ optApplyKeep f := by
  iintro #Hf
  unfold optApplyKeep
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
  isplitr
  · unfold optionsOk at *
    iexact Hok
  ipureintro; simp

/-- A call's `retryOption`s build options. -/
theorem optApplyKeep_of_retryApplyOks (ros : List go_etcd_io.etcd.client.v3.retryOption) :
    ([∗list] ro ∈ ros, retryApplyOk (GF := GF) ro.applyFunc') ⊢
      [∗list] ro ∈ ros, optApplyKeep ro.applyFunc' := by
  induction ros with
  | nil =>
    iintro -
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (ro : go_etcd_io.etcd.client.v3.retryOption) =>
      optApplyKeep (GF := GF) ro.applyFunc')).2
    iempintro
  | cons ro ros ih =>
    iintro H
    icases (BigSepL.bigSepL_cons (Φ := fun _ (ro : go_etcd_io.etcd.client.v3.retryOption) =>
      retryApplyOk (GF := GF) ro.applyFunc')).1 $$ H with ⟨#H1, H2⟩
    iapply (BigSepL.bigSepL_cons (Φ := fun _ (ro : go_etcd_io.etcd.client.v3.retryOption) =>
      optApplyKeep (GF := GF) ro.applyFunc')).2
    isplitl []
    · iapply optApplyKeep_of_retryApplyOk $$ H1
    · iapply ih $$ H2

/-- **A call option the client passes to a stream** (persistent; item 1, the client lease,
2026-10-18): one it passes to a unary call (`callOptOk`), or a `retryOption` whose closure builds
the interceptor's options (`optApplyOk`: the lessor's `withMax(0)`). The stream interceptor applies
the retry options to a copy of its own options and, for a client stream, either retries nothing
(`max` stays `0`) or fails with `Unimplemented` (`retry_interceptor.go`, `NewStream`'s axiom). -/
def streamCallOptOk (v : GoInterface) : IProp GF :=
  iprop(callOptOk v ∨ ∃ ro : go_etcd_io.etcd.client.v3.retryOption,
    ⌜v = interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro⌝ ∗ optApplyOk ro.applyFunc')

instance streamCallOptOk_persistent (v : GoInterface) :
    Persistent (streamCallOptOk (GF := GF) v) := by
  unfold streamCallOptOk; infer_instance

/-- Every call option of `vs` is one the client passes to a stream. -/
def streamCallOptsOk (vs : List GoInterface) : IProp GF := iprop([∗list] v ∈ vs, streamCallOptOk v)

instance streamCallOptsOk_persistent (vs : List GoInterface) :
    Persistent (streamCallOptsOk (GF := GF) vs) := by
  unfold streamCallOptsOk; infer_instance

/-- A unary call's options are a stream's. -/
theorem streamCallOptsOk_of (vs : List GoInterface) :
    callOptsOk (GF := GF) vs ⊢ streamCallOptsOk vs := by
  induction vs with
  | nil =>
    iintro -
    unfold streamCallOptsOk
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons v vs ih =>
    unfold callOptsOk
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hv, Hvs⟩
    unfold streamCallOptsOk
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hv]
    · unfold streamCallOptOk; ileft; iexact Hv
    · have ih' := ih; unfold callOptsOk streamCallOptsOk at ih'
      iapply ih' $$ Hvs

theorem streamCallOptsOk_app (vs ws : List GoInterface) :
    streamCallOptsOk (GF := GF) vs ∗ streamCallOptsOk ws ⊢ streamCallOptsOk (vs ++ ws) := by
  unfold streamCallOptsOk
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [H1]
  · iexact H1
  · iexact H2

theorem streamCallOptsOk_singleton (v : GoInterface) :
    streamCallOptOk (GF := GF) v ⊢ streamCallOptsOk [v] := by
  unfold streamCallOptsOk
  iintro H
  iapply BigSepL.bigSepL_singleton.2
  iexact H

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
