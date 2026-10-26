/-
**The store's in-memory fields, fresh** (the auth plan's E3h, 2026-10-27; `notes/decisions.md`,
"E3h of the auth plan"). Lean-first (no Rocq counterpart).

E3g gave a reader a lower bound of the history's published index (`authPubLb γa i`, `Model.lean`)
and the backend's reads the matching lower bound (`lockedReadTx.specLb`, `ReadLb.lean`). The check
also reads the store's in-memory fields; the store's revision invariant (`revInv`) now holds the
published index's authority with the fields' freshness (`revFresh`, `InvAuth.lean`): the atomic
`revision` is the revision of a state recorded at an index at least the published one. Here: the
verdicts no older than a lower bound (`revisionVerdictFrom`), and `Revision()` read by a reader
holding the lower bound (`Revision.specLb`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__IsAuthEnabled

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section defs
variable [FfiSyntax] {GF : BundledGFunctors} [AllG GF]

/-- **`Revision`'s answer no older than the index `i`** in the mode `M` (persistent): in `on γa`,
the revision of a state recorded at an index at least `i`; as `revisionVerdict` otherwise. -/
def revisionVerdictFrom (M : AuthMode) (i : Nat) (x : w64) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (j : Nat) (st : AuthState), authStateAt γa j st ∗
      ⌜i ≤ j ∧ uint.nat x = st.revision⌝)
  | _ => iprop(True)

instance revisionVerdictFrom_persistent (M : AuthMode) (i : Nat) (x : w64) :
    Persistent (revisionVerdictFrom (GF := GF) M i x) := by
  unfold revisionVerdictFrom; cases M <;> infer_instance

/-- A verdict no older than an index is a verdict. -/
theorem revisionVerdictFrom_verdict (M : AuthMode) (i : Nat) (x : w64) :
    revisionVerdictFrom (GF := GF) M i x ⊢ revisionVerdict M x := by
  cases M with
  | on γa =>
    simp only [revisionVerdictFrom, revisionVerdict]
    iintro ⟨%j, %st, #H, %Hp⟩
    iexists j, st; iframe H; ipureintro; exact Hp.2
  | off => simp only [revisionVerdictFrom, revisionVerdict]; iintro -; itrivial
  | any => simp only [revisionVerdictFrom, revisionVerdict]; iintro -; itrivial

/-- **`IsAuthEnabled`'s answer no older than the index `i`** in the mode `M` (persistent): in
`on γa`, the flag of a state recorded at an index at least `i`; as `enabledVerdict` otherwise. -/
def enabledVerdictFrom (M : AuthMode) (i : Nat) (b : Bool) : IProp GF :=
  match M with
  | .off => iprop(⌜b = false⌝)
  | .any => iprop(True)
  | .on γa => iprop(∃ (j : Nat) (st : AuthState), authStateAt γa j st ∗ ⌜i ≤ j ∧ b = st.enabled⌝)

instance enabledVerdictFrom_persistent (M : AuthMode) (i : Nat) (b : Bool) :
    Persistent (enabledVerdictFrom (GF := GF) M i b) := by
  unfold enabledVerdictFrom; cases M <;> infer_instance

/-- A verdict no older than an index is a verdict. -/
theorem enabledVerdictFrom_verdict (M : AuthMode) (i : Nat) (b : Bool) :
    enabledVerdictFrom (GF := GF) M i b ⊢ enabledVerdict M b := by
  cases M with
  | on γa =>
    simp only [enabledVerdictFrom, enabledVerdict]
    iintro ⟨%j, %st, #H, %Hp⟩
    iexists j, st; iframe H; ipureintro; exact Hp.2
  | off => simp only [enabledVerdictFrom, enabledVerdict]; iintro H; iexact H
  | any => simp only [enabledVerdictFrom, enabledVerdict]; iintro -; itrivial

end defs

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The freshness read by a reader with the lower bound `i`**: the atomic's value is no older
than `i` (the published index is at least the reader's bound, `authPubAuth_lb_le`). -/
theorem revFresh_from (M : AuthMode) (i : Nat) (r : w64) :
    revFresh (GF := GF) M r ⊢ authPubLbM M i -∗ revFresh M r ∗ revisionVerdictFrom M i r := by
  cases M with
  | on γa =>
    simp only [revFresh, authPubLbM, revisionVerdictFrom]
    iintro ⟨%p, Hp, #Hsp, ⟨%j, %s, #Hs, %Hj⟩, Hen⟩ #Hlb
    ihave ⟨⟨Hp, -⟩, %Hle⟩ := ((and_intro (P := iprop(authPubAuth (GF := GF) γa p ∗ authPubLb γa i))
      .rfl (authPubAuth_lb_le γa p i)).trans persistent_and_sep_mp) $$ [Hp]
    · iframe Hp Hlb
    isplitl [Hp Hen]
    · iexists p; iframe Hp Hsp Hen; iexists j, s; iframe Hs; ipureintro; exact Hj
    · iexists j, s; iframe Hs; ipureintro; exact ⟨by omega, Hj.2⟩
  | off => simp only [revFresh, revisionVerdictFrom]; iintro H -; iframe H
  | any => simp only [revFresh, revisionVerdictFrom]; iintro H -; iframe H

/-- **The flag read under `enabledMu`, no older than the reader's lower bound** (the auth plan's
E3h): a share of the field's ghost variable (the guard's) agrees with the store's freshness's
quarter, which is a state's flag at an index at least the published one, itself at least `i`. -/
theorem enG_fresh (st : Loc) (R : IProp GF) (M : AuthMode) (i : Nat) (q : Qp) (b : Bool) :
    authInv (GF := GF) st R M ⊢ enG M q b -∗ enabledVerdict M b -∗ authPubLbM M i ={⊤}=∗
      enG M q b ∗ enabledVerdictFrom M i b := by
  cases M with
  | on γa =>
    iintro #Hinv Hg - #Hlb
    iunfold authInv at Hinv
    icases Hinv with ⟨-, #Hrev, -⟩
    iinv Hrev with Hi Hclose
    iunfold revInv at Hi
    icases Hi with ⟨%r, Hr, Hv, Hc, >Hf⟩
    iunfold revFresh at Hf
    icases Hf with ⟨%p, Hp, #Hsp, Hrv, ⟨%b0, Hq0, %j, %s, #Hs, %Hj⟩, Hcf⟩
    iunfold enG at Hg
    icombine Hg Hq0 gives %Hb0
    obtain ⟨-, Hb0⟩ := Hb0
    subst Hb0
    iunfold authPubLbM at Hlb
    ihave ⟨⟨Hp, -⟩, %Hle⟩ := ((and_intro (P := iprop(authPubAuth (GF := GF) γa p ∗ authPubLb γa i))
      .rfl (authPubAuth_lb_le γa p i)).trans persistent_and_sep_mp) $$ [Hp]
    · iframe Hp Hlb
    imod Hclose $$ [Hr Hv Hc Hp Hrv Hq0 Hcf] with -
    · inext
      iunfold revInv
      iexists r
      iframe Hr Hv Hc
      iunfold revFresh
      iexists p
      iframe Hp Hrv Hsp Hcf
      iexists b
      iframe Hq0
      iexists j, s
      iframe Hs
      ipureintro; exact Hj
    imodintro
    isplitl [Hg]
    · iunfold enG; iexact Hg
    iunfold enabledVerdictFrom
    iexists j, s
    iframe Hs
    ipureintro; exact ⟨by omega, Hj.2⟩
  | off =>
    iintro - Hg #Hv -
    imodintro
    iframe Hg
    simp only [enabledVerdict, enabledVerdictFrom]
    iexact Hv
  | any =>
    iintro - Hg - -
    imodintro
    iframe Hg
    simp only [enabledVerdictFrom]
    itrivial

set_option synthInstance.maxSize 512 in
/-- **Publication** (the auth plan's E3h): the apply thread, after an admin step's batch is committed
(`Unlock`), with the admin side's authority at `hs` whose latest state is `stl`, its halves of the
flag and of the cache with the latest state's flag and permissions (`hb`, `hc`: the tie), raises
the published index to the latest one, `hs.length - 1`, and gets its lower bound (what the waiter's
reply is to carry: a client then holds what it observed). -/
theorem authPublish (st : Loc) (R : IProp GF) (M : AuthMode) (hs : List AuthState) (b : Bool)
    (sc stl : AuthState) (hl : ∀ γa, M = .on γa → hs.getLast? = some stl)
    (hb : ∀ γa, M = .on γa → b = stl.enabled) (hc : ∀ γa, M = .on γa → permView sc = permView stl) :
    authInv (GF := GF) st R M ⊢ authOwn M hs -∗ flagAt st M b -∗ cacheAt st M sc ={⊤}=∗
      authOwn M hs ∗ flagAt st M b ∗ cacheAt st M sc ∗ authPubLbM M (hs.length - 1) := by
  cases M with
  | on γa =>
    have hl := hl γa rfl
    have hb := hb γa rfl
    have hc := hc γa rfl
    iintro #Hinv Hown Hfl Hca
    iunfold flagAt at Hfl
    icases Hfl with ⟨Hfp, Hfq⟩
    iunfold enG at Hfq
    iunfold cacheAt at Hca
    icases Hca with ⟨%mp, %Mp, Hcp, #HM, #Hof, Hcq⟩
    iunfold caA at Hcq
    icases Hcq with ⟨%jc, %sjc, Hcq, #Hsjc, %Hpv⟩
    iunfold authInv at Hinv
    icases Hinv with ⟨-, #Hrev, -⟩
    iinv Hrev with Hi Hclose
    iunfold revInv at Hi
    icases Hi with ⟨%r, Hr, Hv, >Hc, >Hf⟩
    iunfold revFresh at Hf
    icases Hf with ⟨%p, Hp, #Hsp, -, ⟨%b0, Hq0, -⟩, ⟨%v0, Hcq0, -⟩⟩
    icombine Hfq Hq0 gives %Hb0
    obtain ⟨-, Hb0⟩ := Hb0
    subst Hb0
    icombine Hcq Hcq0 gives %Hv0
    obtain ⟨-, Hv0⟩ := Hv0
    subst Hv0
    icases Hsp with ⟨%sp, #Hsp⟩
    ihave ⟨Hown, %stl', %Hl', #Hst⟩ := authOwn_lastAt γa hs p sp $$ [Hown]
    · iframe Hown Hsp
    have hstl : stl' = stl := by rw [hl] at Hl'; exact (Option.some.inj Hl'.1).symm
    -- the atomic is the latest state's revision (the latest state's ghost variable's halves agree)
    iunfold revCur at Hc
    icases Hc with ⟨%stc, Hcur, %Hrc⟩
    iunfold authOwn at Hown
    icases Hown with ⟨Hhh, %stl'', %Hl'', Hcur'⟩
    iunfold authCurHalf at Hcur
    iunfold authCurHalf at Hcur'
    icombine Hcur Hcur' gives %Hcc
    obtain ⟨-, Hcc⟩ := Hcc
    have h2 : stl'' = stl := by rw [hl] at Hl''; exact (Option.some.inj Hl'').symm
    -- the published index raised to the latest one
    iunfold authPubAuth at Hp
    imod (mono_nat_own_update (γ := γa.pub) (hs.length - 1) Hl'.2) $$ Hp with ⟨Hp, #Hlb⟩
    imod Hclose $$ [Hr Hv Hcur Hp Hq0 Hcq0] with -
    · inext
      iunfold revInv
      iexists r
      iframe Hr Hv
      isplitl [Hcur]
      · iunfold revCur; iexists stc; iunfold authCurHalf; iframe Hcur; ipureintro; exact Hrc
      iunfold revFresh
      iexists hs.length - 1
      isplitl [Hp]
      · iunfold authPubAuth; iexact Hp
      isplitl []
      · iexists stl'; iexact Hst
      isplitl []
      · iexists hs.length - 1, stl'; iframe Hst; ipureintro
        refine ⟨Nat.le_refl _, ?_⟩
        rw [Hrc, Hcc, h2, hstl]
      isplitl [Hq0]
      · iexists b; iframe Hq0; iexists hs.length - 1, stl'; iframe Hst; ipureintro
        exact ⟨Nat.le_refl _, by rw [hstl]; exact hb⟩
      iexists (mp, jc); iframe Hcq0; iexists sjc, hs.length - 1, stl'; iframe Hsjc Hst; ipureintro
      exact ⟨Nat.le_refl _, by rw [Hpv, hc, hstl]⟩
    imodintro
    isplitl [Hhh Hcur']
    · iunfold authOwn
      isplitl [Hhh]
      · iexact Hhh
      iexists stl''; iunfold authCurHalf; iframe Hcur'; ipureintro; exact Hl''
    isplitl [Hfp Hfq]
    · iunfold flagAt; iframe Hfp; iunfold enG; iexact Hfq
    isplitl [Hcp Hcq]
    · iunfold cacheAt; iexists mp, Mp; iframe Hcp HM Hof; iunfold caA; iexists jc, sjc; iframe Hcq Hsjc
      ipureintro; exact Hpv
    iunfold authPubLbM; iunfold authPubLb; iexact Hlb
  | off =>
    simp only [authPubLbM]
    iintro - Hown Hfl Hca
    imodintro
    iframe Hown Hfl Hca
  | any =>
    simp only [authPubLbM]
    iintro - Hown Hfl Hca
    imodintro
    iframe Hown Hfl Hca

end ghost

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`Revision()` read by a reader with the lower bound `i`** (the auth plan's E3h): the value is
the revision of a state no older than `i`. -/
def authStore.Revision.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authPubLbM M i }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Revision")) (Val #()))
  {{ (x : w64), RET #x; revisionVerdictFrom M i x }}

theorem authStore.Revision.wp_lb : authStore.Revision.specLb (GF := GF) := by
  intro st R M i
  wp_start as ⟨#Hinv, #Hlb⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, #Hrev, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ]
  · iexact Hatomic
  iinv Hrev with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold revInv at Hi
  icases Hi with ⟨%r, Hr, #Hv, Hc, Hf⟩
  iexists r
  iframe Hr
  iintro Hr
  ihave ⟨Hf, #Hfrom⟩ := revFresh_from M i r $$ Hf Hlb
  imod Hmask with -
  imod Hclose $$ [Hr Hc Hf] with -
  · inext; iunfold revInv; iexists r; iframe Hr Hc Hf; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  iexact Hfrom

/-- **`IsAuthEnabled()` read by a reader with the lower bound `i`** (the auth plan's E3h): the flag
of a state no older than `i`. -/
def authStore.IsAuthEnabled.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      enabledRd st M ∗ authPubLbM M i }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"IsAuthEnabled")) (Val #()))
  {{ (b : Bool), RET #b; enabledRd st M ∗ enabledVerdictFrom M i b }}

theorem authStore.IsAuthEnabled.wp_lb : authStore.IsAuthEnabled.specLb (GF := GF) := by
  intro st R M i
  wp_start as ⟨#Hinv, Hrd, #Hlb⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold enabledRd at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold enabledP at HP
  icases HP with ⟨%b, Hb, #Hv, Hg⟩
  imod (enG_fresh st R M i _ b) $$ Hinv Hg Hv Hlb with ⟨Hg, #Hvf⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hb Hg] as Hrd
  · inext; iunfold enabledP; iexists b; iframe Hb Hg; iexact Hv
  iapply HΦ
  iunfold enabledRd
  iframe Hrd Hvf

end proof

end auth
end EtcdGrove
end Perennial
