/-
Lemmas of `serverWatchStream.isWatchPermitted`'s and `serverWatchStream.recvLoop`'s proofs (G2,
2026-10-30). Lean-first (no Rocq counterpart).

**Each lemma here unfolds another package's definitions** (etcdserver's `srvAuthLb`,
`authStoreLbM`, `principalBoundI`; apply's `isAuthStoreRangeLb`, `permCheck3Lb`, `permCheck3`,
`classResFrom`, `watchClassFrom`, `watchPerms`, `watchKey`; auth's `permVerdictFrom`): they are the
laws those packages lack, kept apart so that each can move to its package as a law.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__isWatchPermitted
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthCheckTxnLb

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- (apply's and auth's law) A passed check's verdict no older than `n` gives the class of its one
permission no older than `n`. -/
theorem v3rpc.classResFrom_of_permVerdictFrom (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (k e : GoString) (op : auth.PermType) :
    auth.permVerdictFrom (GF := GF) M n info k e op GoInterface.nil ⊢
      apply.classResFrom M n info [(k, e, op)] := by
  cases M with
  | off => unfold apply.classResFrom; iintro -; itrivial
  | any => unfold apply.classResFrom; iintro -; itrivial
  | on γa =>
    unfold auth.permVerdictFrom apply.classResFrom
    iintro ⟨⟨%i, %st, #Hst, %Hp⟩, -⟩
    iapply BigSepL.bigSepL_singleton.2
    iexists i, st
    iframe Hst
    ipureintro
    exact ⟨Hp.1, Hp.2 rfl⟩

/-- (apply's law) Outside the mode `on`, the class no older than `n` holds. -/
theorem v3rpc.classResFrom_not_on (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (perms : List apply.Perm3)
    (h : ∀ γa, M ≠ .on γa) : ⊢ apply.classResFrom (GF := GF) M n info perms := by
  cases M with
  | off => unfold apply.classResFrom; itrivial
  | any => unfold apply.classResFrom; itrivial
  | on γa => exact absurd rfl (h γa)

/-- (apply's law) The class of the watch's normalized read is the watch's class. -/
theorem v3rpc.watchClassFrom_of_classResFrom (M : auth.AuthMode) (n : Nat)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (key rangeEnd : GoString) :
    apply.classResFrom (GF := GF) M n info
        [((if key = [] then [W8 0] else key), rangeEnd, auth.PermType.read)] ⊢
      apply.watchClassFrom M n info key rangeEnd := by
  unfold apply.watchClassFrom apply.watchPerms apply.watchKey
  iintro H; iexact H

/-- (apply's law) The watch's normalized key. -/
theorem v3rpc.watchKey_eq (key : GoString) :
    apply.watchKey key = if key = [] then [W8 0] else key := rfl

/-- (etcdserver's law) A checked principal, bound to the context `ctx`, is bound to its token. -/
theorem v3rpc.infoBoundT_of_principalBoundI (s : Loc) (M : auth.AuthMode) (ctx : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    principalBoundI (GF := GF) s M ctx info ⊢ infoBoundT s M (auth.ctxTokenOf ctx) info := by
  unfold principalBoundI infoBoundT principalBound
  iintro H; iexact H

/-- (etcdserver's and apply's law) **The server's range check at a bound `n` of the published
index**: the store of the server's `authStore` field (`isAuthStore`'s `permCheck3`, and with auth
on `srvAuthLb`'s check no older than `n`), its passing verdict the class no older than `n`. -/
theorem v3rpc.srvRangeCheckFrom (s : Loc) (E : apply.AEnv GF) (ai : GoInterfaceOk) (n : Nat) :
    srvAuthStoreAddr s ↦□ (GoInterface.ok ai) ∗ srvAuthLb s E ∗ □ auth.authPubLbM E.authMode n ∗
      apply.permCheck3 ai go!"IsRangePermitted" E.RD E.authMode .read ⊢
    □ (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8)
      (dk de : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ E.RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (App (Val #(methods ai.ty go!"IsRangePermitted" ai.v)) (Val #a)) (Val #key))
        (Val #re))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ E.RD ∗
        authApplyErrIs err ∗
        (⌜err = GoInterface.nil⌝ → apply.classResFrom E.authMode n info [(k, e, .read)]) }}) := by
  iintro ⟨#Hf, #HLb, #Hpub, HP3⟩
  iunfold apply.permCheck3 at HP3
  icases HP3 with #HP3
  cases hM : E.authMode with
  | on γa =>
    iunfold srvAuthLb at HLb
    icases HLb with ⟨%au, #Hf2, #HLbM⟩
    icombine Hf Hf2 gives %Hau
    subst Hau
    rw [hM]
    iunfold authStoreLbM at HLbM
    ihave #HR := HLbM $$ Hpub
    iunfold apply.isAuthStoreRangeLb at HR
    icases HR with ⟨%ai', %Hai', #HP3L⟩
    cases Hai'
    iunfold apply.permCheck3Lb at HP3L
    iintro !> %a %info %dq %key %re %k %e %dk %de
    iintro %Φ !> Hpre HΦ
    iapply HP3L $$ Hpre
    iintro !> %err ⟨Ha, Hk, He, HRD, #Herr, #Hv⟩
    iapply HΦ
    iframe Ha Hk He HRD Herr
    iintro %h
    subst h
    iapply v3rpc.classResFrom_of_permVerdictFrom $$ Hv
  | _ =>
    iintro !> %a %info %dq %key %re %k %e %dk %de
    iintro %Φ !> Hpre HΦ
    iapply HP3 $$ Hpre
    iintro !> %err ⟨Ha, Hk, He, HRD, #Herr, -, -⟩
    iapply HΦ
    iframe Ha Hk He HRD Herr
    iintro -
    iapply v3rpc.classResFrom_not_on
    intro γa h; cases h

end lemmas

end EtcdGrove
end Perennial
