/-
**etcd's specs of the Auth service's admin methods** (the auth plan's E3za, 2026-10-27): the specs
the server registers for `UserAdd`, `UserGrantRole`, `RoleAdd`, `RoleGrantPermission` and
`AuthEnable` (`GrpcSpec`s over the client's wire models, `client/v3/InvAuthConn.lean`), what a run
holds (`authSlot`), and what the server's answers give of them. Lean-first (no Rocq counterpart);
the design is in `notes/decisions.md`, "E3za of the auth plan".

**A reply** (`adminReplied s E ρ tok rq Q`, persistent): the request `rq` the client asked for (at
some header, its wire form `rq'`) was applied at the committed prefix `L` before its entry, its
admin step succeeding there (`adminDoneM`), the auth state after it published (`pubAfterM`), its
step determinate there and, if its entry is recorded in the auth history, the result `Q` of the
client's update (`adminQh`), the header bound to the call's token `tok` (`hdrBoundT`): what
`raftRequest.spec` with auth on answers on success (`adminOutOn`), less the response's memory and the
store's certificates. For `UserAdd`, some model of the request with the name asked for, the
password choice `false` (the client sends no options) and a password that cannot fail
(`userAddReplied`).

**The specs** (metadata-indexed: the auth-mode merge's 5b, 2026-10-29) ask the client for its
update of the auth history (`histAu`, at the header bound to the attempt's token; for `UserAdd`,
at every model of the request), the names' bound the server's admission needs (`maxKeySize`), and
the caller's postcondition from the reply. The server holds the rest: per run
its slot (`authSlot`: a reader slot of `s.leadTimeMu` and the apply environment's `E.RD`, both
back on every answer), the id budget and the index certificate (minted, `idxCert_nil`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a run of an Auth admin method holds** (see the file header). -/
def authSlot (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ E.RD)

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **What a successful admin call of `rq` tells the client** (persistent; see the file
header). -/
def adminReplied (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (L : List EntryModel),
    ⌜irrWireOf (apply.withHeader rq hm) rq' ∧ adminDoneM true ρ.kv rq' L⌝ ∗
    srvRLogLb ρ.raft L ∗ pubAfterM true E ρ rq' L ∗ adminQh ρ.kv rq Q hm L ∗
    hdrBoundT T E.authMode tok hm)

instance adminReplied_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (adminReplied T E ρ tok rq Q) := by
  unfold adminReplied adminQh adminPropRes; infer_instance

/-- **What a successful `UserAdd` of `name` tells the client** (persistent; see the file
header). -/
def userAddReplied (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (name : GoString) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ um : apply.UserAddModel, ⌜um.name = name ∧ um.noPassword = false ∧ um.pwSure⌝ ∗
    adminReplied T E ρ tok (irrUserAdd um) Q)

instance userAddReplied_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (name : GoString) (Q : List auth.AuthState → IProp GF) :
    Persistent (userAddReplied T E ρ tok name Q) := by
  unfold userAddReplied; infer_instance

/-- **A client's update of the auth history by `rq`, at the token `tok`** (persistent; 5b):
`histAu` with the header bound to `tok` (`hdrBoundT`). -/
def authHistAuT (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) : IProp GF :=
  histAu ρ.raft ρ.kv srvAuthSt0 (hdrBoundT T E.authMode tok) rq Q

instance authHistAuT_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    Persistent (authHistAuT T E ρ tok rq Q) := by
  unfold authHistAuT; infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `Auth.UserAdd`** (see the file header). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdUserAddSpecW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcMd → UserAddW → (Unit → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (m : UserAddW) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : List auth.AuthState → IProp GF, ⌜m.name.length ≤ backend.maxKeySize⌝ ∗
      □ (∀ um : apply.UserAddModel, ⌜um.name = m.name ∧ um.noPassword = false ∧ um.pwSure⌝ →
        authHistAuT T E ρ (auth.mdTokenOf md) (irrUserAdd um) Q) ∗
      (userAddReplied T E ρ (auth.mdTokenOf md) m.name Q -∗ Φ ()))

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`etcdUserAddSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec
is `etcdUserAddSpecW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdUserAddSpec (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse :=
  etcdUserAddSpecW T E ρ

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `Auth.UserGrantRole`** (see the file header). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdUserGrantRoleSpecW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcMd → GoString × GoString → (Unit → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (ur : GoString × GoString) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : List auth.AuthState → IProp GF, ⌜ur.1.length ≤ backend.maxKeySize⌝ ∗
      authHistAuT T E ρ (auth.mdTokenOf md) (irrUserGrantRole ur.1 ur.2) Q ∗
      (adminReplied T E ρ (auth.mdTokenOf md) (irrUserGrantRole ur.1 ur.2) Q -∗ Φ ()))

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`etcdUserGrantRoleSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdUserGrantRoleSpecW`, over the models alone, what a service table holds; this is its
form at the message types). -/
def etcdUserGrantRoleSpec (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse :=
  etcdUserGrantRoleSpecW T E ρ

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `Auth.RoleAdd`** (see the file header). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdRoleAddSpecW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcMd → GoString → (Unit → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (name : GoString) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : List auth.AuthState → IProp GF, ⌜name.length ≤ backend.maxKeySize⌝ ∗
      authHistAuT T E ρ (auth.mdTokenOf md) (irrRoleAdd name) Q ∗
      (adminReplied T E ρ (auth.mdTokenOf md) (irrRoleAdd name) Q -∗ Φ ()))

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`etcdRoleAddSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec
is `etcdRoleAddSpecW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdRoleAddSpec (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse :=
  etcdRoleAddSpecW T E ρ

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `Auth.RoleGrantPermission`** (see the file header). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdRoleGrantPermissionSpecW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcMd → GoString × auth.PermW → (Unit → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (nw : GoString × auth.PermW) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : List auth.AuthState → IProp GF, ⌜nw.1.length ≤ backend.maxKeySize⌝ ∗
      authHistAuT T E ρ (auth.mdTokenOf md) (irrRoleGrantPermission nw.1 (some nw.2)) Q ∗
      (adminReplied T E ρ (auth.mdTokenOf md) (irrRoleGrantPermission nw.1 (some nw.2)) Q -∗
        Φ ()))

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`etcdRoleGrantPermissionSpecW` at the messages' models** (S2, heap-free vocabulary,
2026-11-23: the spec is `etcdRoleGrantPermissionSpecW`, over the models alone, what a service table
holds; this is its form at the message types). -/
def etcdRoleGrantPermissionSpec (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse :=
  etcdRoleGrantPermissionSpecW T E ρ

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `Auth.AuthEnable`** (see the file header). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdAuthEnableSpecW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcMd → Unit → (Unit → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (_ : Unit) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ Q : List auth.AuthState → IProp GF,
      authHistAuT T E ρ (auth.mdTokenOf md) irrAuthEnable Q ∗
      (adminReplied T E ρ (auth.mdTokenOf md) irrAuthEnable Q -∗ Φ ()))

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`etcdAuthEnableSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdAuthEnableSpecW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdAuthEnableSpec (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) :
    GrpcSpecMd (GF := GF) pbAuthEnableRequest pbAuthEnableResponse :=
  etcdAuthEnableSpecW T E ρ

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The server's update from the client's** at the call's token: the bound the server
stamps a header under (`hdrBoundM true`) is `hdrBoundT`'s (`hdrBoundM_tok`). -/
theorem adminHistAu_of_tok (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    authHistAuT (GF := GF) (srvTLSId s) E ρ tok rq Q ⊢
      adminHistAu s E ρ tok rq Q := by
  unfold authHistAuT adminHistAu
  exact histAu_mono _ _ _ _ _ _ _ (fun hm => hdrBoundM_tok s E _ hm)

/-- **An admin answer gives the run's slot back and, on success, the reply** (`adminOutOn`'s
success: `appliedOkM true`'s `adminDoneM`, the log's bound, the publication, the step's
determinacy and the history update's result, the header's bound). -/
theorem adminOutOn_reply (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (F : mvcc.Log) (T : go.GoType) (l : Loc) (err : GoInterface) :
    adminOutOn s E ρ tok rq F (adminQh ρ.kv rq Q) T l err ⊢
      authSlot s E ∗
        (⌜err = GoInterface.nil⌝ -∗ adminReplied (srvTLSId s) E ρ tok rq Q) := by
  iintro H
  iunfold adminOutOn at H
  icases H with ⟨Hlt, Hrd, H⟩
  unfold authSlot
  icases H with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hap, #Hpub, #Hq, #Hhb⟩ | ⟨%He, -⟩)
  · iunfold appliedOkM at Hap
    icases Hap with ⟨%x, %x', %o, %skip, %Hp, -⟩
    iframe Hlt Hrd
    iintro -
    unfold adminReplied
    iexists hm, rq', L
    ihave #Hhb' := hdrBoundM_tok s E _ hm $$ Hhb
    iframe #
    ipureintro; exact ⟨Hw, Hp.2.2.2.2⟩
  · iframe Hlt Hrd
    iintro %He'
    exact absurd He' He

/-- **The `AuthServer`'s answer to an admin request** (`authWrapOut` over `adminOutOn`): the slot
back and, on `nil`, the reply. -/
theorem authWrapOut_admin (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF)
    (F : mvcc.Log) (T : go.GoType) (resp : Loc) (err : GoInterface) :
    authWrapOut (adminOutOn s E ρ tok rq F (adminQh ρ.kv rq Q) T) resp err ⊢
      authSlot s E ∗
        (⌜err = GoInterface.nil⌝ -∗ adminReplied (srvTLSId s) E ρ tok rq Q) := by
  iintro H
  iunfold authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, -, %e0, %He0, H⟩)
  · subst He
    iapply (adminOutOn_reply s E ρ tok rq Q F T resp GoInterface.nil) $$ H
  · ihave ⟨Hs, -⟩ := adminOutOn_reply s E ρ tok rq Q F T null e0 $$ H
    iframe Hs
    iintro %He
    exact absurd He Hr.2

/-- **An admin request's answer without an error is a response, not `nil`** (`adminOutOn`'s
`appliedOkM`, `dispatchAnswer_admin_nn`). -/
theorem adminOutOn_nn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (F : mvcc.Log)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (T : go.GoType) (l : Loc)
    (hT : adminRespTy (apply.dispatchKind rq) = some T) :
    adminOutOn s E ρ tok rq F Qh T l GoInterface.nil ⊢ ⌜l ≠ null⌝ := by
  iintro H
  iunfold adminOutOn at H
  icases H with ⟨-, -, H⟩
  icases H with (⟨-, %hm, %rq', %L, %Hw, -, Hap, -⟩ | ⟨%He, -⟩)
  · iunfold appliedOkM at Hap
    icases Hap with ⟨%x, %x', %o, %skip, -, Hans, -⟩
    have hT' : adminRespTy (apply.dispatchKind rq') = some T := by rw [Hw.2.2.1]; exact hT
    iapply (dispatchAnswer_admin_nn rq' x.log skip null o T l hT') $$ Hans
  · exact absurd rfl He

/-- **The `AuthServer`'s answer to an admin request is not `nil` without an error.** -/
theorem authWrapOut_admin_nn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Qh : apply.HeaderModel → List EntryModel → IProp GF)
    (F : mvcc.Log) (T : go.GoType) (resp : Loc) (err : GoInterface)
    (hT : adminRespTy (apply.dispatchKind rq) = some T) :
    authWrapOut (adminOutOn s E ρ tok rq F Qh T) resp err ⊢
      ⌜err = GoInterface.nil → resp ≠ null⌝ := by
  iintro H
  iunfold authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, -⟩)
  · subst He
    ihave %Hn := adminOutOn_nn s E ρ tok rq F Qh T resp hT $$ H
    ipureintro; intro _; exact Hn
  · ipureintro; intro He; exact absurd He Hr.2

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-! ### O2: monotonicity in the TLS fact (2026-11-23) -/

open Iris.ProofMode in
theorem adminReplied_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ adminReplied T1 E ρ tok rq Q ⊢ adminReplied T2 E ρ tok rq Q := by
  unfold adminReplied
  iintro ⟨#HT, %hm, %rq', %L, %h, Hl, Hp, Hq, Hb⟩
  iexists hm, rq', L
  isplitr
  · ipureintro; exact h
  iframe Hl Hp Hq
  iapply hdrBoundT_mono T1 T2
  iframe HT Hb

open Iris.ProofMode in
theorem userAddReplied_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (name : GoString) (Q : List auth.AuthState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ userAddReplied T1 E ρ tok name Q ⊢ userAddReplied T2 E ρ tok name Q := by
  unfold userAddReplied
  iintro ⟨#HT, %um, %h, H⟩
  iexists um
  isplitr
  · ipureintro; exact h
  iapply adminReplied_mono T1 T2
  iframe HT H

open Iris.ProofMode in
/-- A caller's update told the header bound at `T2` is one told it at `T1`. -/
theorem authHistAuT_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (rq : apply.IRRModel) (Q : List auth.AuthState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ authHistAuT T2 E ρ tok rq Q ⊢ authHistAuT T1 E ρ tok rq Q := by
  unfold authHistAuT
  exact histAu_mono_with _ _ _ _ _ _ _ _ (fun hm => hdrBoundT_mono T1 T2 E.authMode tok hm)

open Iris.ProofMode in
/-- (O2) **`Auth.UserAdd`'s spec is antitone in the TLS fact**: a registration at `T1` serves a
caller at `T2` when `T1` gives `T2` (`isGrpcRpcMd_mono`). -/
theorem etcdUserAddSpecW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (md : GrpcMd)
    (m : UserAddW) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdUserAddSpecW T2 E ρ md m Φ Ψe ⊢ etcdUserAddSpecW T1 E ρ md m Φ Ψe := by
  unfold etcdUserAddSpecW
  iintro ⟨#HT, He, %Q, %hl, #Ha, Hk⟩
  iframe He
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl []
  · imodintro
    iintro %um %h
    iapply authHistAuT_mono T1 T2
    iframe HT
    iapply Ha $$ %um %h
  iintro Hr
  iapply Hk
  iapply userAddReplied_mono T1 T2
  iframe HT Hr

open Iris.ProofMode in
theorem etcdUserGrantRoleSpecW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (md : GrpcMd)
    (ur : GoString × GoString) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdUserGrantRoleSpecW T2 E ρ md ur Φ Ψe ⊢
      etcdUserGrantRoleSpecW T1 E ρ md ur Φ Ψe := by
  unfold etcdUserGrantRoleSpecW
  iintro ⟨#HT, He, %Q, %hl, Ha, Hk⟩
  iframe He
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Ha]
  · iapply authHistAuT_mono T1 T2
    iframe HT Ha
  iintro Hr
  iapply Hk
  iapply adminReplied_mono T1 T2
  iframe HT Hr

open Iris.ProofMode in
theorem etcdRoleAddSpecW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (md : GrpcMd)
    (name : GoString) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdRoleAddSpecW T2 E ρ md name Φ Ψe ⊢ etcdRoleAddSpecW T1 E ρ md name Φ Ψe := by
  unfold etcdRoleAddSpecW
  iintro ⟨#HT, He, %Q, %hl, Ha, Hk⟩
  iframe He
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Ha]
  · iapply authHistAuT_mono T1 T2
    iframe HT Ha
  iintro Hr
  iapply Hk
  iapply adminReplied_mono T1 T2
  iframe HT Hr

open Iris.ProofMode in
theorem etcdRoleGrantPermissionSpecW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (md : GrpcMd) (nw : GoString × auth.PermW) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdRoleGrantPermissionSpecW T2 E ρ md nw Φ Ψe ⊢
      etcdRoleGrantPermissionSpecW T1 E ρ md nw Φ Ψe := by
  unfold etcdRoleGrantPermissionSpecW
  iintro ⟨#HT, He, %Q, %hl, Ha, Hk⟩
  iframe He
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Ha]
  · iapply authHistAuT_mono T1 T2
    iframe HT Ha
  iintro Hr
  iapply Hk
  iapply adminReplied_mono T1 T2
  iframe HT Hr

open Iris.ProofMode in
theorem etcdAuthEnableSpecW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (md : GrpcMd)
    (u : Unit) (Φ : Unit → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdAuthEnableSpecW T2 E ρ md u Φ Ψe ⊢ etcdAuthEnableSpecW T1 E ρ md u Φ Ψe := by
  unfold etcdAuthEnableSpecW
  iintro ⟨#HT, He, %Q, Ha, Hk⟩
  iframe He
  iexists Q
  isplitl [Ha]
  · iapply authHistAuT_mono T1 T2
    iframe HT Ha
  iintro Hr
  iapply Hk
  iapply adminReplied_mono T1 T2
  iframe HT Hr

end monoT

end lemmas

end v3rpc
end EtcdGrove
end Perennial
