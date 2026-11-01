/-
**The auth store's catch-up at a snapshot install (Draft; `notes/snapshot-auth-on-plan.md`, Q1 (b)).**
Imported by nothing; no `axiom`, no `sorry`.

With auth on, a member that installs a snapshot jumps from the auth state of its applied prefix `A`
to the image's, the state after `A'`, skipping the admin entries between. The server's tie of the
store's history to the log (`authHistTie`) keeps the history a *prefix* of the committed log's
admin states (`bootState :: admStates … A`); option (b) keeps it so by appending every skipped
state, then the image's, in one step.

**Not a ghost-only step.** The latest state's ghost variable (`authCurHalf`, both halves: the
admin side's `authOwnF` and the `revision` atomic's invariant `revCur`) is tied to the atomic's
value (`revCur`'s `uint.nat r = st.revision`): moving the latest state without the atomic's store
breaks it. So the catch-up happens where `Recover` stores the new revision (`setRevision`), as a
list append: `authOwnF_revCur_appendL` below, the list form of `authOwnF_revCur_append` (which
`setRevision`'s proof uses, at `opt.length ≤ 1`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section ghost
variable [GooseExts] {GF : BundledGFunctors} [AllG GF]

/-- **`authHist_append` for a list** of states. -/
theorem auth.authHist_appendL (γa : AuthNames) (hs L : List AuthState)
    (hk : ∀ st ∈ L, permKeysOk st) : authHist (GF := GF) γa hs ∗ authHistRev γa hs ⊢
      |==> (authHist γa (hs ++ L) ∗ authHistRev γa (hs ++ L)) := by
  unfold authHist
  iintro ⟨⟨H, %Hk⟩, Hr⟩
  ihave H := (authHist_full γa hs).2 $$ [H Hr]
  · iframe H Hr
  imod (monoListAuthOwn_update_app (γ := γa.hist) (l := hs) L) $$ H with ⟨H, -⟩
  icases (authHist_full γa (hs ++ L)).1 $$ H with ⟨H, Hr⟩
  imodintro
  iframe H Hr
  ipureintro
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Hk x hx
  · exact hk x hx

end ghost

section ghost2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The admin side appends the skipped states `L`, then `st'`**, while the atomic is set to
`st'`'s revision (the list form of `authOwnF_revCur_append`): in `on γa` the history grows by
`L ++ [st']` and both halves of the latest state's ghost variable move to `st'` (the states of `L`
are recorded, never latest); in `off` the states stay disabled; in `any` nothing. The cap's
permission is one lower bound at the whole new history (`capNext M (hs ++ L) st'`), which covers
every intermediate prefix. -/
theorem auth.authOwnF_revCur_appendL (M : AuthMode) (hs L : List AuthState) (st' : AuthState)
    (r r' : w64)
    (hk : M.isOn = true → M ≠ .any → ∀ x ∈ L ++ [st'], permKeysOk x)
    (hoff : M = .off → ∀ x ∈ L ++ [st'], x.enabled = false)
    (hr' : M.isOn = true → M ≠ .any → uint.nat r' = st'.revision) :
    ⊢ authOwnF (GF := GF) M hs -∗ revCur M r -∗ capNext M (hs ++ L) st' -∗
      |==> (authOwnF M (hs ++ L ++ [st']) ∗ revCur M r' ∗ revisionVerdict M r') := by
  cases M with
  | on γa =>
    simp only [authOwnF, revCur, revisionVerdict, capNext]
    iintro ⟨Hh, ⟨%stl, %Hl, Hc1⟩⟩ ⟨%stc, Hc2, -, %hh, Hq, -⟩ #Hcap
    ihave %Hhh := authHist_rev_agree γa hs hh $$ Hh Hq
    subst Hhh
    imod (authCurHalf_update γa stl stc st') $$ Hc1 Hc2 with ⟨Hc1, Hc2⟩
    imod (auth.authHist_appendL γa hs (L ++ [st']) (hk rfl (by intro h; cases h))) $$ [Hh Hq]
      with ⟨Hh, Hq⟩
    · iframe Hh Hq
    rw [← List.append_assoc]
    imod (authHist_stateAt_keep γa (hs ++ L ++ [st']) (hs ++ L).length st'
      (by simp)) $$ Hh with ⟨Hh, #Hst⟩
    imodintro
    iframe Hh
    isplitl [Hc1]
    · iexists st'; iframe Hc1; ipureintro; simp
    isplitl [Hc2 Hq]
    · iexists st'; iframe Hc2; isplitr
      · ipureintro; exact hr' rfl (by intro h; cases h)
      · iexists hs ++ L ++ [st']; iframe Hq
        rw [List.append_assoc]; iexact Hcap
    · iexists (hs ++ L).length, st'; iframe Hst; ipureintro; exact hr' rfl (by intro h; cases h)
  | off =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro %H - -
    imodintro
    isplitr
    · ipureintro
      refine ⟨by simp, ?_⟩
      intro x hx
      rw [List.append_assoc] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact H.2 x hx
      · exact hoff rfl x hx
    · isplitr <;> itrivial
  | any =>
    simp only [authOwnF, revCur, revisionVerdict]
    iintro - - -
    imodintro
    isplitr; itrivial; isplitr; itrivial; itrivial

/-- **The cap's permission for a whole new history** `C` (persistent): in `on γa`, one lower bound of
the cap at `C`, which covers every prefix (`capLb_le`); in the other modes nothing. What the
catch-up's tie half gives (`authHistTie_catchup`, `etcdserver/SnapAuthOnDraft.lean`). -/
def auth.capAtM (M : AuthMode) (C : List AuthState) : IProp GF :=
  match M with
  | .on γa => capLb γa C
  | _ => iprop(True)

instance auth.capAtM_persistent (M : AuthMode) (C : List AuthState) :
    Persistent (auth.capAtM (GF := GF) M C) := by
  unfold auth.capAtM; cases M <;> infer_instance

/-- **The admin side appends any list `N` of states**, the atomic set to the new latest state's
revision (`N` empty: `authOwnF_revCur_keep`; else `authOwnF_revCur_appendL` at `N`'s last). -/
theorem auth.authOwnF_revCur_appendN (M : AuthMode) (hs N : List AuthState) (stl : AuthState)
    (r r' : w64) (hl : histLast M (hs ++ N) stl)
    (hk : M.isOn = true → M ≠ .any → ∀ x ∈ N, permKeysOk x)
    (hoff : M = .off → ∀ x ∈ N, x.enabled = false)
    (hr' : M.isOn = true → M ≠ .any → uint.nat r' = stl.revision) :
    ⊢ authOwnF (GF := GF) M hs -∗ revCur M r -∗ auth.capAtM M (hs ++ N) -∗
      |==> (authOwnF M (hs ++ N) ∗ revCur M r' ∗ revisionVerdict M r') := by
  rcases List.eq_nil_or_concat N with hN | ⟨L, x, hN⟩
  · subst hN
    rw [List.append_nil] at hl ⊢
    iintro Ho Hc -
    iapply (authOwnF_revCur_keep M hs stl r r' hl hr') $$ Ho Hc
  · subst hN
    simp only [List.concat_eq_append] at hl hk hoff ⊢
    have hxr : M.isOn = true → M ≠ .any → uint.nat r' = x.revision := by
      intro h1 h2
      cases M with
      | on γa =>
        simp only [histLast, ← List.append_assoc, List.getLast?_append, List.getLast?_singleton,
          Option.some_or] at hl
        cases hl; exact hr' h1 h2
      | off => cases h1
      | any => exact absurd rfl h2
    have e : hs ++ (L ++ [x]) = hs ++ L ++ [x] := (List.append_assoc _ _ _).symm
    rw [e]
    iintro Ho Hc #Hcap
    iapply (auth.authOwnF_revCur_appendL M hs L x r r' hk hoff hxr) $$ Ho Hc [Hcap]
    cases M with
    | on γa => simp only [auth.capAtM, capNext]; iexact Hcap
    | off => simp only [capNext]; itrivial
    | any => simp only [capNext]; itrivial

end ghost2

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.setRevision(rev)` appending any list `opt`** (the catch-up's form of
`setRevision.spec`, which allows at most one state): the cap's permission at the whole new history
(`capAtM`), the states' keys valid (on) or disabled (off), `rev` the new latest state's
revision. -/
abbrev auth.authStore.setRevision.specN : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (rev : w64) (hs opt : List AuthState) (stl : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwnF M hs ∗ auth.capAtM M (hs ++ opt) ∗
      ⌜histLast M (hs ++ opt) stl ∧ uint.nat rev = stl.revision ∧
        (∀ x ∈ opt, (M.isOn = true → M ≠ .any → permKeysOk x) ∧ (M = .off → x.enabled = false))⌝ }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"setRevision")) (Val #rev))
  {{ RET #(); authOwnF M (hs ++ opt) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.setRevision.wp_proofN :
    auth.authStore.setRevision.specN (GF := GF) (hG := hG) := by
  intro st R M rev hs opt stl
  wp_start as ⟨#Hinv, Hown, #Hcap, %Hp⟩
  obtain ⟨Hlast, Hrev, Hopt⟩ := Hp
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, #Hrevinv, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ Hown]
  · iexact Hatomic
  iinv Hrevinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold revInv at Hi
  icases Hi with ⟨%r, Hr, -, Hc, Hf⟩
  iexists r
  iframe Hr
  iintro Hr
  imod (auth.authOwnF_revCur_appendN M hs opt stl r rev Hlast
    (fun h1 h2 x hx => (Hopt x hx).1 h1 h2) (fun h x hx => (Hopt x hx).2 h) (fun _ _ => Hrev))
    $$ Hown Hc Hcap with ⟨Hown, Hc, #Hv⟩
  imod (authOwnF_revFresh M (hs ++ opt) stl r rev (fun γa h => by subst h; exact Hlast)
    (fun _ _ => Hrev)) $$ Hown Hf with ⟨Hown, Hf⟩
  imod Hmask with -
  imod Hclose $$ [Hr Hc Hf] with -
  · inext; iunfold revInv; iexists rev; iframe Hr Hc Hf; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  iexact Hown

end proof

end EtcdGrove
end Perennial
