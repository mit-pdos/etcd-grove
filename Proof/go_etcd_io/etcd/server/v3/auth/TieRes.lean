/-
**The apply thread's tie as a resource of the history** (the auth plan's E2v, 2026-10-26;
`notes/decisions.md`, "E2v of the auth plan"). E2s's `X.specT` keep the admin side's halves of the
flag and the cache tied to the latest state (`tieStep`) with the halves' values exposed in the write
resource (`authWRx`). Along the apply layer's admin chain the store's write resource is a constant
(`W`, borrowed and given back), while the tie depends on the history the step produces. So the tie
moves to the authority's side: `tieRes st M hs` (the halves at the values tied to `hs`'s latest
state), carried with the authority (`authOwnT`), and a step's result is stated for an authority
family `Own` (`adminOutX`; `adminOut` and E2l's `adminOutFu` are its instances, `adminOut_eq_X`,
`adminOutFu_eq_X`). What stays constant is `authWB` (the store's half of `be` with the backend's
write contract, and the write token).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.LatestTie
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

namespace auth

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An outcome's resource for the authority family `Own`** (`outRes`'s, `Steps.lean`). -/
def outResX (Own : List AuthState → IProp GF) (hs : List AuthState) (o : Outcome)
    (err : GoInterface) : IProp GF :=
  match o with
  | .err e => iprop(Own hs ∗ authErrOf e err)
  | .same => iprop(Own hs ∗ ⌜err = GoInterface.nil⌝)
  | .next st' => iprop(Own (hs ++ [st']) ∗ ⌜err = GoInterface.nil⌝)

/-- **An admin operation's result for the authority family `Own`** (`adminOut`'s, `Steps.lean`):
the outcome of `R` at the latest state with `Own` at the history after it, or an `extra` error. -/
def adminOutX (M : AuthMode) (Own : List AuthState → IProp GF) (hs : List AuthState) (R : StepRel)
    (extra : AuthErr → Prop) (err : GoInterface) : IProp GF :=
  iprop((∃ e : AuthErr, ⌜extra e⌝ ∗ Own hs ∗ authErrOf e err) ∨
    (∃ (st : AuthState) (o : Outcome), ⌜histLast M hs st ∧ R st o⌝ ∗ outResX Own hs o err))

theorem outRes_eq_X (M : AuthMode) (hs : List AuthState) (o : Outcome) (err : GoInterface) :
    outRes (GF := GF) M hs o err = outResX (authOwn M) hs o err := by
  cases o <;> rfl

theorem adminOut_eq_X (M : AuthMode) (hs : List AuthState) (R : StepRel) (extra : AuthErr → Prop)
    (err : GoInterface) :
    adminOut (GF := GF) M hs R extra err = adminOutX M (authOwn M) hs R extra err := by
  unfold adminOut adminOutX
  simp only [outRes_eq_X]

theorem outResFu_eq_X (γa : AuthNames) (hs : List AuthState) (o : Outcome) (err : GoInterface) :
    outResFu (GF := GF) γa hs o err = outResX (authOwnFu γa) hs o err := by
  cases o <;> rfl

theorem adminOutFu_eq_X (γa : AuthNames) (hs : List AuthState) (R : StepRel)
    (extra : AuthErr → Prop) (err : GoInterface) :
    adminOutFu (GF := GF) γa hs R extra err = adminOutX (.on γa) (authOwnFu γa) hs R extra err := by
  unfold adminOutFu adminOutX
  simp only [outResFu_eq_X]

/-- **`adminOutX` is monotone in the authority family.** -/
theorem adminOutX_mono (M : AuthMode) (Own Own' : List AuthState → IProp GF) (hs : List AuthState)
    (R : StepRel) (extra : AuthErr → Prop) (err : GoInterface)
    (h : ∀ h, Own h ⊢ Own' h) :
    adminOutX M Own hs R extra err ⊢ adminOutX M Own' hs R extra err := by
  unfold adminOutX
  iintro (⟨%e, %He, Ho, Herr⟩ | ⟨%st, %o, %Ho, Hr⟩)
  · ileft; iexists e; iframe Herr
    isplitr
    · ipureintro; exact He
    iapply (h hs) $$ Ho
  · iright; iexists st, o
    isplitr
    · ipureintro; exact Ho
    cases o <;> simp only [outResX] <;> icases Hr with ⟨Hr, Hx⟩ <;> iframe Hx
    · iapply (h hs) $$ Hr
    · iapply (h hs) $$ Hr
    · iapply (h _) $$ Hr

/-- **The step's result with the fuel back** (`adminOut_fu`, for an authority family with an
extra resource `X` of the history). -/
theorem adminOutX_fu (γa : AuthNames) (X : List AuthState → IProp GF) (hs : List AuthState)
    (R : StepRel) (extra : AuthErr → Prop) (err : GoInterface) (hR : StepSmall R) :
    authFuelT (GF := GF) hs ∗ adminOutX (.on γa) (fun h => iprop(authOwn (.on γa) h ∗ X h)) hs R
      extra err ⊢ adminOutX (.on γa) (fun h => iprop(authOwnFu γa h ∗ X h)) hs R extra err := by
  iintro ⟨Hf, Ho⟩
  unfold adminOutX
  dsimp only
  icases Ho with (⟨%e, %He, ⟨Hown, HX⟩, Herr⟩ | ⟨%st, %o, %Hst, Hres⟩)
  · ileft
    iexists e
    ihave Hf := authFuelT_keep hs $$ Hf
    isplitr
    · ipureintro; exact He
    iframe HX Herr
    iunfold authOwnFu; iframe Hown Hf
  · iright
    iexists st, o
    isplitr
    · ipureintro; exact Hst
    cases o with
    | err e =>
      simp only [outResX, authOwnFu]
      icases Hres with ⟨⟨Hown, HX⟩, Herr⟩
      ihave Hf := authFuelT_keep hs $$ Hf
      iframe Hown Hf HX Herr
    | same =>
      simp only [outResX, authOwnFu]
      icases Hres with ⟨⟨Hown, HX⟩, Herr⟩
      ihave Hf := authFuelT_keep hs $$ Hf
      iframe Hown Hf HX Herr
    | next st' =>
      simp only [outResX, authOwnFu]
      icases Hres with ⟨⟨Hown, HX⟩, Herr⟩
      ihave Hf := authFuelT_next hs R st st' hR Hst.1 Hst.2 $$ Hf
      iframe Hown Hf HX Herr

/-- **The halves tied to the latest state of `hs`** (see the file header): the flag's half at `b`
(with its verdict) and the cache's half at `sc` (a recorded state), `latestTie M hs b sc`. -/
def tieRes (st : Loc) (M : AuthMode) (hs : List AuthState) : IProp GF :=
  iprop(∃ (b : Bool) (sc : AuthState), flagAt st M b ∗ enabledVerdict M b ∗ cacheAt st M sc ∗
    authSnap M sc ∗ ⌜latestTie M hs b sc⌝)

/-- **The authority with the tie** (see the file header). -/
@[reducible] def authOwnT (st : Loc) (M : AuthMode) (hs : List AuthState) : IProp GF :=
  iprop(authOwn M hs ∗ tieRes st M hs)

/-- **The store's write resource but the halves** (see the file header): the store's half of `be`
with the backend's write contract, and the write token. -/
def authWB (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) : IProp GF :=
  iprop((∃ be : AuthBackend, aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗ authWBackendOk be M P f T) ∗
    T)

/-- The write resource with exposed halves is `authWB` with the halves. -/
theorem authWRx_split (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) (b : Bool)
    (sc : AuthState) :
    authWRx (GF := GF) st M P f T b sc ⊢
      authWB st M P f T ∗ flagAt st M b ∗ enabledVerdict M b ∗ cacheAt st M sc ∗ authSnap M sc := by
  unfold authWRx authWB
  iintro ⟨Hbe, HT, Hfl, #Hev, Hca, #Hs⟩
  iframe Hbe HT Hfl Hev Hca Hs

theorem authWRx_join (st : Loc) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF) (b : Bool)
    (sc : AuthState) :
    authWB (GF := GF) st M P f T ∗ flagAt st M b ∗ enabledVerdict M b ∗ cacheAt st M sc ∗
      authSnap M sc ⊢ authWRx st M P f T b sc := by
  unfold authWRx authWB
  iintro ⟨⟨Hbe, HT⟩, Hfl, #Hev, Hca, #Hs⟩
  iframe Hbe HT Hfl Hev Hca Hs

/-- **A tie-keeping step's result is `adminOutX` for `authOwnT`**: the halves after the step, tied
by `tieStep` from the halves before (tied to `hs`), are tied to the history after. -/
theorem adminOutP_tieRes (st : Loc) (M : AuthMode) (hs : List AuthState) (R : StepRel)
    (extra : AuthErr → Prop) (err : GoInterface) (b0 : Bool) (sc0 : AuthState) (b : Bool)
    (sc : AuthState) (ht : latestTie M hs b0 sc0) :
    flagAt (GF := GF) st M b ∗ enabledVerdict M b ∗ cacheAt st M sc ∗ authSnap M sc ∗
      adminOutP M hs R extra err (tieStep M hs b0 sc0 b sc) ⊢
      adminOutX M (authOwnT st M) hs R extra err := by
  iintro ⟨Hfl, #Hev, Hca, #Hs, Hout⟩
  unfold adminOutP adminOutX
  icases Hout with (⟨%e, %Hp, %Hx, Ho, Herr⟩ | ⟨%s, %o, %Hp, %Hr, Hres⟩)
  · ileft; iexists e; iframe Herr
    isplitr
    · ipureintro; exact Hx
    unfold authOwnT tieRes
    iframe Ho
    iexists b, sc
    iframe Hfl Hev Hca Hs
    ipureintro; exact Hp ht
  · iright; iexists s, o
    isplitr
    · ipureintro; exact Hr
    cases o with
    | err e =>
      simp only [outRes, outResX, histAfter] at *
      icases Hres with ⟨Ho, Herr⟩
      iframe Herr
      unfold authOwnT tieRes
      iframe Ho
      iexists b, sc
      iframe Hfl Hev Hca Hs
      ipureintro; exact Hp ht
    | same =>
      simp only [outRes, outResX, histAfter] at *
      icases Hres with ⟨Ho, Herr⟩
      iframe Herr
      unfold authOwnT tieRes
      iframe Ho
      iexists b, sc
      iframe Hfl Hev Hca Hs
      ipureintro; exact Hp ht
    | next st' =>
      simp only [outRes, outResX, histAfter] at *
      icases Hres with ⟨Ho, Herr⟩
      iframe Herr
      unfold authOwnT tieRes
      iframe Ho
      iexists b, sc
      iframe Hfl Hev Hca Hs
      ipureintro; exact Hp ht

/-- **`latestRes` of the tie** (E2s's resource for the checks at the latest state). -/
theorem latestRes_of_T (st : Loc) (M : AuthMode) (hs : List AuthState) :
    authOwnT (GF := GF) st M hs ⊢ latestRes st M hs ∗ ∃ (b : Bool) (sc : AuthState),
      enabledVerdict M b ∗ authSnap M sc := by
  unfold authOwnT tieRes latestRes
  iintro ⟨Ho, %b, %sc, Hfl, #Hev, Hca, #Hs, %Ht⟩
  isplitl [Ho Hfl Hca]
  · iframe Ho; iexists b, sc; iframe Hfl Hca Hev Hs; ipureintro; exact Ht
  iexists b, sc; iframe Hev Hs

/-- **`latestRes` is the authority with the tie** (E3f). -/
theorem authOwnT_of_latestRes (st : Loc) (M : AuthMode) (hs : List AuthState) :
    latestRes (GF := GF) st M hs ⊢ authOwnT st M hs := by
  unfold authOwnT tieRes latestRes
  iintro ⟨Ho, %b, %sc, Hfl, Hca, #Hev, #Hs, %Ht⟩
  iframe Ho; iexists b, sc; iframe Hfl Hca Hev Hs; ipureintro; exact Ht

/-- **The authority with the tie lends the checks' latest-state resource** (E3f; the lending
`apply.Apply.adminSpecL`'s `hsplit` asks of the authority family, and the KV checks'). -/
theorem authOwnT_lend (st : Loc) (M : AuthMode) (hs : List AuthState) :
    authOwnT (GF := GF) st M hs ⊢ latestRes st M hs ∗ (latestRes st M hs -∗ authOwnT st M hs) := by
  iintro H
  ihave ⟨H, -⟩ := latestRes_of_T st M hs $$ H
  iframe H
  iintro H
  iapply authOwnT_of_latestRes st M hs $$ H

/-- **The fueled authority with the tie lends the latest-state resource** (E3f; the apply
thread's authority family, `authOwnFu` with `tieRes`, the `hsplit` of `apply.Apply.adminSpecL` and
the lending of the KV checks' `L hs`). -/
theorem ownFuT_lend (st : Loc) (γa : AuthNames) (hs : List AuthState) :
    authOwnFu (GF := GF) γa hs ∗ tieRes st (.on γa) hs ⊢
      latestRes st (.on γa) hs ∗
        (latestRes st (.on γa) hs -∗ authOwnFu γa hs ∗ tieRes st (.on γa) hs) := by
  unfold authOwnFu
  iintro ⟨⟨Ho, Hf⟩, Ht⟩
  ihave ⟨HL, Hback⟩ := authOwnT_lend st (.on γa) hs $$ [Ho Ht]
  · unfold authOwnT; iframe Ho Ht
  iframe HL
  iintro HL
  ihave H := Hback $$ HL
  unfold authOwnT
  icases H with ⟨Ho, Ht⟩
  iframe Ho Hf Ht

/-- A pure consequence kept beside its premise. -/
theorem keep_pure {A : IProp GF} {φ : Prop} (h : A ⊢ ⌜φ⌝) : A ⊢ A ∗ ⌜φ⌝ :=
  (and_intro (by iintro H; iexact H) h).trans persistent_and_sep_mp

/-- **The tie at a history of disabled states** (the store's start: `NewAuthStore`'s
`[bootState, bump bootState]`): the flag's half is `false` (its verdict is a recorded state's flag,
and the admin side's half of the history holds every recorded state), and the cache's state, a
recorded one, has the latest state's permissions when the history's states all have the same
(`hpv`, the auth plan's E3j), so the halves are tied. -/
theorem tieRes_of_disabled (st : Loc) (γa : AuthNames) (hs : List AuthState)
    (hdis : ∀ s ∈ hs, s.enabled = false)
    (hpv : ∀ s ∈ hs, ∀ s' ∈ hs, permView s = permView s') :
    authOwn (GF := GF) (.on γa) hs ∗ enabledHalf st (.on γa) ∗ cacheHalf st (.on γa) ⊢
      authOwn (.on γa) hs ∗ tieRes st (.on γa) hs := by
  iintro ⟨Ho, Hen, Hca⟩
  iunfold enabledHalf at Hen
  icases Hen with ⟨%b, Hfl, #Hev⟩
  iunfold cacheHalf at Hca
  icases Hca with ⟨%sc, Hca, #Hs⟩
  ihave #Hev' := Hev
  iunfold enabledVerdict at Hev'
  icases Hev' with ⟨%i, %st', #Hat, %Hb⟩
  iunfold authOwn at Ho
  icases Ho with ⟨Hh, Hc⟩
  ihave Hk := (keep_pure (authHistHalf_lookup (GF := GF) γa hs i st')) $$ [Hh]
  · iframe Hh Hat
  icases Hk with ⟨⟨Hh, -⟩, %Hi⟩
  have hb : b = false := by rw [Hb]; exact hdis st' (List.mem_of_getElem? Hi)
  ihave #Hs' := Hs
  iunfold authSnap at Hs'
  icases Hs' with ⟨%j, #Hj⟩
  ihave Hk2 := (keep_pure (authHistHalf_lookup (GF := GF) γa hs j sc)) $$ [Hh]
  · iframe Hh Hj
  icases Hk2 with ⟨⟨Hh, -⟩, %Hj'⟩
  isplitl [Hh Hc]
  · iunfold authOwn
    isplitl [Hh]
    · iexact Hh
    iexact Hc
  iunfold tieRes
  iexists b, sc
  iframe Hfl Hev Hca Hs
  ipureintro
  intro stl hl
  refine ⟨?_, fun h => absurd (hb ▸ h) (by simp),
    hpv sc (List.mem_of_getElem? Hj') stl (List.mem_of_getLast? hl)⟩
  rw [hb, hdis stl (List.mem_of_getLast? hl)]

end res

end auth

end EtcdGrove
end Perennial
