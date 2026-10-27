/-
**The permission checks' wrappers no older than a reader's lower bound, and publication from the
tie** (the auth plan's E3j, 2026-10-27; `notes/decisions.md`, "E3j of the auth plan"). Lean-first
(no Rocq counterpart).

`IsPutPermitted`, `IsRangePermitted` and `IsDeleteRangePermitted` call `isOpPermitted` with the
principal's fields and the operation; for a reader holding a lower bound `n` of the published index
(`authPubLbM`, E3g) their verdict is `isOpPermitted.specLb`'s (E3h), at states no older than `n`
(`permVerdictFrom`). They are what the read path checks (`doSerialize`'s `chk`: `Range`'s
`IsRangePermitted`), beside the apply thread's latest-state forms (`*.specL`, `Latest.lean`).

`authPublishT` is E3h's `authPublish` with its hypotheses on the halves taken from the tie
(`latestTie`, which since E3j carries the cache's permissions always).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.FreshCheck

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

namespace auth

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **Publication from the tie** (the auth plan's E3j): `authPublish`, its halves' hypotheses (the
latest state's flag and permissions) from `latestTie`. -/
theorem authPublishT (st : Loc) (R : IProp GF) (M : AuthMode) (hs : List AuthState) (b : Bool)
    (sc stl : AuthState) (hl : ∀ γa, M = .on γa → hs.getLast? = some stl)
    (ht : latestTie M hs b sc) :
    authInv (GF := GF) st R M ⊢ authOwn M hs -∗ flagAt st M b -∗ cacheAt st M sc ={⊤}=∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗ authPubLbM M (hs.length - 1) :=
  authPublish st R M hs b sc stl hl
    (fun γa h => by subst h; exact (ht stl (hl γa rfl)).1)
    (fun γa h => by subst h; exact (ht stl (hl γa rfl)).2.2)

end ghost

end auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

open auth

/-- `as.IsPutPermitted(authInfo, key)` read by a reader with the lower bound `n`: the verdict on
the write at states no older than `n`. -/
abbrev auth.authStore.IsPutPermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (info : AuthInfo) (dq : DFrac)
    (key : GoSlice) (k : List w8) (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗
      authPubLbM M n }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsPutPermitted")) (Val #a)) (Val #key))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ authErrIs err ∗
      permVerdictFrom M n info k [] .write err }}

/-- `as.IsRangePermitted(authInfo, key, rangeEnd)` read by a reader with the lower bound `n` (the
read path's check): the verdict on the read at states no older than `n`. -/
abbrev auth.authStore.IsRangePermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (info : AuthInfo) (dq : DFrac)
    (key re : GoSlice) (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗
      authPubLbM M n }}
    (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsRangePermitted")) (Val #a)) (Val #key)) (Val #re))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗
      re ↦*{de} e ∗ authErrIs err ∗ permVerdictFrom M n info k e .read err }}

/-- `as.IsDeleteRangePermitted(authInfo, key, rangeEnd)` read by a reader with the lower bound `n`:
the verdict on the write at states no older than `n`. -/
abbrev auth.authStore.IsDeleteRangePermitted.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) (a : Loc) (info : AuthInfo) (dq : DFrac)
    (key re : GoSlice) (k e : List w8) (dk de : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ ∗
      authPubLbM M n }}
    (App (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsDeleteRangePermitted")) (Val #a)) (Val #key)) (Val #re))
  {{ (err : GoInterface), RET #err; authRd st R M ∗ a ↦{dq} info ∗ key ↦*{dk} k ∗
      re ↦*{de} e ∗ authErrIs err ∗ permVerdictFrom M n info k e .write err }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

open auth

theorem auth.authStore.IsPutPermitted.wp_lb
    (h_isOpPermitted : auth.authStore.isOpPermitted.specLb (GF := GF)) :
    auth.authStore.IsPutPermitted.specLb (GF := GF) := by
  intro st R M n a info dq key k dk
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, %Hlen, #Hlb⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M n info key slice.nil k [] dk (DFrac.own 1)
      (W32 1)) $$ [$Hinv $Hrd $Hk $Hlb] as %err ⟨Hrd, Hk, -, Herr, #Hv⟩
  · isplitl
    · iapply ownSlice_nil (V := w8) (DFrac.own 1)
    ipureintro; exact ⟨by simp [permTypOk], Hlen⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  iExactEq Hv
  all_goals simp [permOp]

theorem auth.authStore.IsRangePermitted.wp_lb
    (h_isOpPermitted : auth.authStore.isOpPermitted.specLb (GF := GF)) :
    auth.authStore.IsRangePermitted.specLb (GF := GF) := by
  intro st R M n a info dq key re k e dk de
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, He, %Hlen, #Hlb⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M n info key re k e dk de
      (W32 0)) $$ [$Hinv $Hrd $Hk $He $Hlb] as %err ⟨Hrd, Hk, He, Herr, #Hv⟩
  · ipureintro; exact ⟨by simp [permTypOk], Hlen⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  iExactEq Hv
  all_goals simp [permOp]

theorem auth.authStore.IsDeleteRangePermitted.wp_lb
    (h_isOpPermitted : auth.authStore.isOpPermitted.specLb (GF := GF)) :
    auth.authStore.IsDeleteRangePermitted.specLb (GF := GF) := by
  intro st R M n a info dq key re k e dk de
  wp_start as ⟨#Hinv, Hrd, Ha, Hk, He, %Hlen, #Hlb⟩
  ihave %Hann := typedPointsto_not_null $$ Ha
  iStructNamed Ha
  wp_auto
  wp_apply (h_isOpPermitted st R M n info key re k e dk de
      (W32 1)) $$ [$Hinv $Hrd $Hk $He $Hlb] as %err ⟨Hrd, Hk, He, Herr, #Hv⟩
  · ipureintro; exact ⟨by simp [permTypOk], Hlen⟩
  ihave Ha : a ↦{dq} info $$ [Username Revision]
  · iapply typedPointsto_combine a info dq Hann
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iframe
  iExactEq Hv
  all_goals simp [permOp]

end proof

end EtcdGrove
end Perennial
