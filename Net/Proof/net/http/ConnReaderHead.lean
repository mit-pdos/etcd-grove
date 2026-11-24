/-
The connection reader (`ConnReader.lean`) while the server reads a request's head through its
buffered reader (`connReader.Read`, 2026-11-23, `notes/dsverify-net-port-plan.md`, phase 5.2): the
stream state `crHead cr γ γe cn P Q L c r` of `io.readerStreamNE`, `r` the bytes the reader has
delivered:

* the main phase (the main thread's half of `γ.ph` at "main": the mutex invariant holds only the
  background reader's token), the fields owned: the connection `c`, no byte kept, no read running,
  the read limit `remain` at `L - len(r)` (`L` the server's `initialReadLimitSize`);
* the acceptor's send token with nothing written (`sendTok cn true Q []`), which with `headLaw` and
  `zLaw` makes what the dialer wrote a prefix of the head (`crHead_prefix`);
* the reader's token at `r`, and the end's read deadline not set (`rdlTok cn true false`: no read
  times out);
* the once-cell `γe` (a monotone list): empty while no read has returned an error, `[r]` once one
  did at `r`, and then the reader delivers nothing more: the connection's reading is dead
  (`readDead`, the net extension's sticky read errors, D1 v3.5: `read_after_dead_au`), or the read
  limit is reached (`io.EOF` again).

Its read error predicate is `crHeadErr γe` (a read returned the error `e` at `r`, persistent:
`io.EOF`'s `*errorString` or the connection's `*OpError` of a read, `crErrId e`, whose `Error()`
returns some string other than `"message too large"`, `errMsgOk e`), whose finality (`crHeadErr_final`: nothing delivered after it) and message
(`crHeadErr_msg`) are what a head parser's spec asks (`readRequestLimit.spec`).

Before and after the head, the reader is in the main phase with its read limit at any `v`:
`crMain cr γ cn P Q c r v` (the fields, `remain` at `v`, the tokens at `r`). `conn.readRequest`
sets the limit to `L` (`setReadLimit`), starts the head at `r = []` (`crMain_head`: a fresh
once-cell), reads it, leaves it (`crHead_main`) and lifts the limit (`setInfiniteReadLimit`:
`v = maxInt64`), so the background read (`startBackgroundRead`) starts from `crMain`.
-/
module

public import Net.Proof.net.http.ConnReader
public import Net.Proof.net.http.RequestDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Net

namespace net.http

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
def crHead (cr : Loc) (γ : CrNames) (γe : GName) (cn : Nat) (P Q : Proto GF) (L : Nat) (c : Loc)
    (r : List w8) : IProp GF :=
  iprop(ghostVar γ.ph (1 : Qp).half false ∗ ⌜r.length ≤ L⌝ ∗
    ∃ ab : Bool,
    structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
    structFieldRef net.http.connReader go!"hasByte" cr ↦ false ∗
    structFieldRef net.http.connReader go!"inRead" cr ↦ false ∗
    structFieldRef net.http.connReader go!"aborted" cr ↦ ab ∗
    structFieldRef net.http.connReader go!"remain" cr ↦ (W64 (L - r.length : Nat)) ∗
    (∃ arr : GoArray w8 1, structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr) ∗
    sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗
    recvTok (Gg := hG.goose_globalGS) cn true P r ∗ rdlTok (Gg := hG.goose_globalGS) cn true false ∗
    ((monoListAuthOwn γe 1 [r] ∗ (readDead (Gg := hG.goose_globalGS) cn true ∨ ⌜r.length = L⌝)) ∨
      monoListAuthOwn γe 1 ([] : List (List w8))))

/-- See the file header. -/
def crErrId (e : GoInterface) : IProp GF :=
  iprop((∃ xe : Loc, ⌜e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe⌝ ∗
          globalAddr io.EOF ↦□ e) ∨
        (∃ src addr e' : GoInterface, net.opErr go!"read" src addr e' e))

instance crErrId_persistent (e : GoInterface) : Persistent (crErrId (GF := GF) e) := by
  unfold crErrId; infer_instance

/-- See the file header. -/
def crHeadErr (γe : GName) : List w8 → GoInterface → IProp GF := fun r e =>
  iprop(monoListLbOwn γe [r] ∗ errMsgOk e ∗ crErrId e)

/-- See the file header. -/
def crMain (cr : Loc) (γ : CrNames) (cn : Nat) (P Q : Proto GF) (c : Loc) (r : List w8) (v : w64) :
    IProp GF :=
  iprop(ghostVar γ.ph (1 : Qp).half false ∗
    ∃ ab : Bool,
    structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
    structFieldRef net.http.connReader go!"hasByte" cr ↦ false ∗
    structFieldRef net.http.connReader go!"inRead" cr ↦ false ∗
    structFieldRef net.http.connReader go!"aborted" cr ↦ ab ∗
    structFieldRef net.http.connReader go!"remain" cr ↦ v ∗
    (∃ arr : GoArray w8 1, structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr) ∗
    sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗
    recvTok (Gg := hG.goose_globalGS) cn true P r ∗ rdlTok (Gg := hG.goose_globalGS) cn true false)

instance crHeadErr_persistent (γe : GName) (r : List w8) (e : GoInterface) :
    Persistent (crHeadErr (GF := GF) γe r e) := by
  unfold crHeadErr; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- What the reader has delivered is a prefix of the head (`headLaw`), the acceptor having written
nothing (`zLaw`). -/
theorem crHead_prefix (cr : Loc) (γ : CrNames) (γe : GName) (cn : Nat) (P Q : Proto GF)
    (hs : List w8) (Z : Nat → IProp GF) (L : Nat) (c : Loc) (r : List w8) :
    headLaw P hs Z ∗ zLaw Z Q ∗ crHead cr γ γe cn P Q L c r ⊢ ⌜r <+: hs⌝ := by
  unfold headLaw zLaw crHead
  iintro ⟨#Hlaw, #Hz, -, -, %ab, -, -, -, -, -, -, Hsend, Hrecv, -⟩
  icases recvTok_proto (Gg := hG.goose_globalGS) cn true _ _ $$ Hrecv with ⟨-, #Hpp⟩
  unfold protoPrefix
  icases Hpp with (%h | ⟨%ext, %hext, #HP⟩)
  · subst h; ipureintro; exact List.nil_prefix
  · icases Hlaw $$ %cn %ext HP with (%h | HZ)
    · ipureintro; exact hext.trans h
    · iexfalso; iapply Hz $$ %cn HZ Hsend

/-- After an error at `r`, the reader stays at `r`. -/
theorem crHeadErr_final (cr : Loc) (γ : CrNames) (γe : GName) (cn : Nat) (P Q : Proto GF)
    (L : Nat) (c : Loc) (r r' : List w8) (e : GoInterface) :
    crHeadErr γe r e ∗ crHead cr γ γe cn P Q L c r' ⊢ ⌜r <+: r' → r' = r⌝ := by
  unfold crHeadErr crHead
  iintro ⟨⟨#He, -, -⟩, -, -, %ab, -, -, -, -, -, -, -, -, -, Hc⟩
  icases Hc with (⟨Hc, -⟩ | Hc)
  · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hc He
    obtain ⟨-, Hp⟩ := Hv
    ipureintro
    intro _
    obtain ⟨t, ht⟩ := Hp
    cases t with
    | nil => simpa using ht.symm
    | cons _ _ => simp at ht
  · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hc He
    obtain ⟨-, Hp⟩ := Hv
    exact absurd (List.prefix_nil.1 Hp) (by simp)

/-- A read error's message: what `readRequestLimit.spec` asks of its stream's errors. -/
theorem crHeadErr_msg (γe : GName) :
    ⊢ (□ ∀ (r : List w8) (e : GoInterface), crHeadErr γe r e -∗ errMsgOk e : IProp GF) := by
  unfold crHeadErr
  imodintro
  iintro %r %e ⟨-, #H, -⟩
  iexact H

/-- The head started at `[]`, the limit set to `L`: a fresh once-cell. -/
theorem crMain_head (cr : Loc) (γ : CrNames) (cn : Nat) (P Q : Proto GF) (L : Nat) (c : Loc) :
    crMain cr γ cn P Q c [] (W64 L) ⊢ |==> ∃ γe, crHead cr γ γe cn P Q L c [] := by
  unfold crMain crHead
  iintro ⟨Hph, %ab, Hc, Hhb, Hir, Hab, Hrm, Hbuf, Hsend, Hrecv, Hrdl⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (List w8)) with ⟨%γe, He, -⟩
  imodintro
  iexists γe
  iframe Hph
  isplitr
  · ipureintro; simp
  iexists ab
  iframe Hc Hhb Hir Hab Hbuf Hsend Hrecv Hrdl
  isplitl [Hrm]
  · simp only [List.length_nil, Nat.sub_zero]; iexact Hrm
  iright; iexact He

/-- The head left: the main phase, the limit at `L - len(r)`. -/
theorem crHead_main (cr : Loc) (γ : CrNames) (γe : GName) (cn : Nat) (P Q : Proto GF) (L : Nat)
    (c : Loc) (r : List w8) :
    crHead cr γ γe cn P Q L c r ⊢ crMain cr γ cn P Q c r (W64 (L - r.length : Nat)) := by
  unfold crMain crHead
  iintro ⟨Hph, -, %ab, Hc, Hhb, Hir, Hab, Hrm, Hbuf, Hsend, Hrecv, Hrdl, -⟩
  iframe Hph
  iexists ab
  iframe

end lemmas

end net.http
end Perennial
