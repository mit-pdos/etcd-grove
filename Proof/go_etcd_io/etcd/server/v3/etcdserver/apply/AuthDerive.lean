/-
The apply package's auth-store contract (`apply.isAuthStore`), its request-side part, of the real
auth store, from the auth store's proofs (2026-10-14, unit P2). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`.

`isAuthStore`'s permission clauses (`IsPutPermitted`, `IsRangePermitted`,
`IsDeleteRangePermitted`, `IsAdminPermitted`) and `IsAuthEnabled` take no resource (`{{ True }}`
and the caller's slices), but the real methods read-lock `enabledMu` and `rangePermCacheMu` and
the backend's read transaction, each an `RWMutex` whose readers Perennial bounds (a reader slot,
`sync.ownRWMutex`, per concurrent reader): not derivable as stated. `isAuthStorePerms st RD`
states them with a reader resource `RD` the caller holds and gets back (the shape of the request
path's `waitOk w RD`), and the permission checks with the key below `2^63 - 1`
(`NewBytesAffinePoint`'s `make([]byte, len(key)+1)`: no slice in memory reaches it, but the
model's `make` does not assume it); `isAuthStorePerms_of_authInv` derives it of the real store,
with `RD := auth.authRd st R`. `Revision` is derived as `isAuthStore` states it
(`authRevision_of_authInv`). The store's errors are the package's `errors.New` variables
(`auth.authErrVar`, the shape of `errVarLeaf`): `applyErrIs` (`authErrIs_applyErrIs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsPutPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsRangePermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsDeleteRangePermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAdminPermitted
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `permCheck2` with the caller's reader resource `RD` and the key's length bound. -/
def permCheck2R (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key : GoSlice) (k : List w8)
      (dk : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ RD ∗ applyErrIs err }}))

/-- `permCheck3` with the caller's reader resource `RD` and the key's length bound. -/
def permCheck3R (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8)
      (dk de : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗
        applyErrIs err }}))

/-- **`isAuthStore`'s request-side clauses with a reader resource** `RD` (see the file header):
the three permission checks, `IsAdminPermitted`, `IsAuthEnabled`, and `Revision` (as
`isAuthStore` states it). -/
def isAuthStorePerms (st : GoInterface) (RD : IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    permCheck2R ai go!"IsPutPermitted" RD ∗
    permCheck3R ai go!"IsRangePermitted" RD ∗
    permCheck3R ai go!"IsDeleteRangePermitted" RD ∗
    □ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac),
      {{ a ↦{dq} info ∗ RD }} (App (Val #(methods ai.ty go!"IsAdminPermitted" ai.v)) (Val #a))
      {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ RD ∗ applyErrIs err }}) ∗
    □ ({{ RD }} (App (Val #(methods ai.ty go!"IsAuthEnabled" ai.v)) (Val #()))
      {{ (b : Bool), RET #b; RD }}) ∗
    □ ({{ True }} (App (Val #(methods ai.ty go!"Revision" ai.v)) (Val #()))
      {{ (x : w64), RET #x; True }}))

instance isAuthStorePerms_persistent (st : GoInterface) (RD : IProp GF) :
    Persistent (isAuthStorePerms st RD) := by
  unfold isAuthStorePerms permCheck2R permCheck3R; infer_instance

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- An auth-store error is one `errors.Is` can take. -/
theorem authErrIs_applyErrIs (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      auth.authErrIs err ⊢ applyErrIs err := by
  iintro ⟨#Hpkg, #Herr⟩
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨#HUE, #HUNF, #HPD, #HOR, #HIT, -, -⟩
  iunfold auth.authErrIs at Herr
  icases Herr with (%Hnil | ⟨%g, %e, %Hg, #Hge, %He⟩)
  · subst Hnil; iapply applyErrIs_nil
  ihave #Hv : errVarLeaf (GF := GF) g $$ []
  · rcases Hg with rfl | rfl | rfl | rfl | rfl
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HUE
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HUE
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HUNF
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HUNF
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HPD
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HPD
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HOR
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HOR
    · iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HIT
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact HIT
  iapply errVar_applyErrIs g err $$ Hv
  iexists e; iframe Hge; ipureintro; exact He

/-- **`isAuthStore`'s `Revision` clause, of the real store** (as the contract states it). -/
theorem authRevision_of_authInv
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R ⊢
      □ ({{ True }} (App (Val #(methods (go.GoType.PointerType auth.authStore.ty) go!"Revision"
          #st)) (Val #()))
        {{ (x : w64), RET #x; True }}) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iintro !> %Φ !> - HΦ
  iapply (hRev st R) $$ [] HΦ
  iframe Hpkg Hinv

/-- **`isAuthStore`'s request-side clauses, of the real store** at `st` (`auth.authInv st R`),
with the reader resource `auth.authRd st R` (see the file header). -/
theorem isAuthStorePerms_of_authInv
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R ⊢
      isAuthStorePerms (auth.authIface st) (auth.authRd st R) := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold isAuthStorePerms
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  isplitr
  · iunfold permCheck2R
    iintro !> %a %info %dq %key %k %dk %Φ !> ⟨Ha, Hk, Hrd, %Hlen⟩ HΦ
    iapply (hPut st R a info dq key k dk) $$ [Ha Hk Hrd]
    · iframe; iframe #; ipureintro; exact Hlen
    iintro !> %err ⟨Hrd, Ha, Hk, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iunfold permCheck3R
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, %Hlen⟩ HΦ
    iapply (hRange st R a info dq key re k e dk de) $$ [Ha Hk He Hrd]
    · iframe; iframe #; ipureintro; exact Hlen
    iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iunfold permCheck3R
    iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, %Hlen⟩ HΦ
    iapply (hDel st R a info dq key re k e dk de) $$ [Ha Hk He Hrd]
    · iframe; iframe #; ipureintro; exact Hlen
    iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iintro !> %a %info %dq %Φ !> ⟨Ha, Hrd⟩ HΦ
    iapply (hAdmin st R a info dq) $$ [Ha Hrd]
    · iframe; iframe #
    iintro !> %err ⟨Hrd, Ha, #Herr⟩
    iapply HΦ
    iframe
    iapply authErrIs_applyErrIs err $$ [$Hpkg $Herr]
  isplitr
  · iintro !> %Φ !> Hrd HΦ
    iunfold auth.authRd at Hrd
    icases Hrd with ⟨Hen, Hca, HR⟩
    iapply (hEn st R) $$ [Hen]
    · iframe; iframe #
    iintro !> %b Hen
    iapply HΦ
    iunfold auth.authRd
    iframe
  · iapply authRevision_of_authInv hRev st R $$ [$Hpkg $Hinv]

end proof

end apply
end EtcdGrove
end Perennial
