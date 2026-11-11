/-
Selftests of `etc/AxiomTokCheck.lean` (the `axiom-tok` gate, the Scope's §5.1 "Selftests"). Not a
module of the build (`etc/` is outside every `lean_lib` glob) and has no header: the checker
elaborates it over the modules `etc/axiom-tok-check.py --selftest` imports, then judges the axioms
it declares. An axiom named `st_refuse_*` must get a finding, one named `st_pass_*` none; the other
axioms are the toys' vocabulary (opaque predicates). Rule 7's pair cases use
`etc/axiom-tok-selftest/allow.txt`; real axioms of today's trust base the main run must pass are the
`real-pass` lines of that file.
-/
namespace AxiomTokSelftest
open Perennial Iris Iris.BI

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! Refused -/

/-- `{{ True }} f {{ threadTok }}`: a mint (rule 2). -/
axiom st_refuse_mint : ∀ (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); threadTok }}

/-- A nested-callback mint: the axiom hands `k` a token nobody gave it (rule 2). -/
axiom st_refuse_callback : ∀ (f k : val),
  ({{ threadTok (GF := GF) }} (App (Val k) (Val #())) {{ RET #(); True }}) →
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); True }}

/-- D1's revert text (`notes/lease-ex-plan.md:52-56`): each run gets `S ∗ threadTok`, the caller
gives only the `n` copies of `S` (rule 2: the handler's returned token pays nothing, it may block). -/
axiom stServes (h : val) : IProp GF
axiom st_refuse_d1 : ∀ (S : IProp GF) (n : Nat) (h : val),
  ([∗list] _x ∈ List.replicate n (), S) ∗
    □ ({{ S ∗ threadTok }} (App (Val h) (Val #())) {{ RET #(); S ∗ threadTok }}) ⊢
  |={⊤}=> stServes (GF := GF) h

/-- `∀ R, {{ True }} f {{ R }}` (rule 3). -/
axiom st_refuse_param : ∀ (R : IProp GF) (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); R }}

/-- A persistent mint: `□ (True -∗ threadTok)` (rule 2, through `□`). -/
axiom st_refuse_pers : ⊢ □ (iprop(True) -∗ threadTok (GF := GF))

/-- A fake holder: its producer consumes nothing (rule 6). -/
axiom stFake (l : Loc) : IProp GF
axiom st_fake_mk : ∀ (l : Loc), ⊢ |==> stFake (GF := GF) l
axiom st_refuse_fake_use : ∀ (l : Loc), stFake (GF := GF) l ⊢ |==> threadTok

/-- An `∃ P` produced with no declared pair (rule 7). -/
axiom st_refuse_exists : ⊢ |==> ∃ (P : IProp GF), P

/-- A pair whose partner consumes a different type (rule 7; `allow.txt` declares the pair). -/
axiom st_refuse_pairtype : ⊢ |==> ∃ (P : Nat → IProp GF), P 0
axiom st_partner_bad : ∀ (Q : Bool → IProp GF), Q true ⊢ |==> True

/-- More levels: `levelTok 1` from `levelTok 0` (rule 2, per level). -/
axiom st_refuse_level : ∀ (f : val),
  {{ levelTok (GF := GF) 0 }} (App (Val f) (Val #())) {{ RET #(); levelTok 1 }}

/-- A symbolic count picked by the user (rule 1). -/
axiom st_refuse_sym : ∀ (n : Nat) (f : val),
  {{ threadToks (GF := GF) 1 }} (App (Val f) (Val #())) {{ RET #(); threadToks n }}

/-- m2: a model-only name with a `FuncUnfold` (the run reports `modelUnfold`). -/
axiom st_refuse_unfold : FuncUnfold go!"google.golang.org/grpc#model.acceptRun" [] (#())

/-- Entries are finding-specific (CP1a review M2; `allow.txt`): an entry naming another key than
the finding's does not accept it. -/
axiom st_refuse_entrykey : ∀ (R : IProp GF) (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); R }}

/-- An entry accepting one of two findings leaves the other. -/
axiom st_refuse_entrypart : ∀ (R S : IProp GF) (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); R ∗ S }}

/-- A rule-7 entry names the binder's type: another type is not accepted. -/
axiom st_refuse_entrytype : ⊢ |==> ∃ (P : Bool → IProp GF), P true

/-- An entry names the count: `R` produced twice is not `R` produced once. -/
axiom st_refuse_entrycount : ∀ (R : IProp GF) (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); R ∗ R }}

/-- A single mint's entry does not accept the mint turned persistent. -/
axiom st_refuse_entrypers : ⊢ □ (iprop(True) -∗ threadTok (GF := GF))

/-- A single mint's entry does not accept a token handed to a callback. -/
axiom st_refuse_entrycb : ∀ (S : IProp GF) (n : Nat) (h : val),
  ([∗list] _x ∈ List.replicate n (), S) ∗
    □ ({{ S ∗ threadTok }} (App (Val h) (Val #())) {{ RET #(); S ∗ threadTok }}) ⊢
  |={⊤}=> stServes (GF := GF) h

/-! Passed -/

/-- Token in, token out (as `lessor.Renew`/`leaseTimeToLive`'s `levelTok 0`). -/
axiom st_pass_level : ∀ (f : val),
  {{ levelTok (GF := GF) 0 }} (App (Val f) (Val #())) {{ RET #(); levelTok 0 }}

/-- `∀ R, {{ R }} f {{ R }}`. -/
axiom st_pass_frame : ∀ (R : IProp GF) (f : val),
  {{ R }} (App (Val f) (Val #())) {{ RET #(); R }}

/-- A token split into its levels. -/
axiom st_pass_split : threadTok (GF := GF) ⊢ |==> levelTok 0 ∗ threadTokFrom 1

/-- A callback contract that is balanced, taking a token from the caller. -/
axiom st_pass_callback : ∀ (f k : val),
  ({{ threadTok (GF := GF) }} (App (Val k) (Val #())) {{ RET #(); threadTok }}) →
  {{ threadTok (GF := GF) }} (App (Val f) (Val #())) {{ RET #(); threadTok }}

/-- A real holder (rule 6: as the begin-tok pairs). -/
axiom stHold (l : Loc) : IProp GF
axiom st_pass_hold_mk : ∀ (l : Loc), threadTok (GF := GF) ⊢ |==> stHold l
axiom st_pass_hold_use : ∀ (l : Loc), stHold (GF := GF) l ⊢ |==> threadTok

/-- An `∃` produced only inside an opaque handle (rule 7's first case). -/
axiom stHandle (P : IProp GF) : IProp GF
axiom st_pass_exhandle : ⊢ |==> ∃ (P : IProp GF), stHandle P

/-- A pair whose partner consumes the type, at an address-indexed family (rule 7; `allow.txt`). -/
axiom st_pass_pair : ⊢ |==> ∃ (P : Nat → IProp GF), P 0
axiom st_partner_ok : ∀ (Q : GoString → Nat → IProp GF) (a : GoString), Q a 0 ⊢ |==> True

/-- A user-picked symbolic count, balanced. -/
axiom st_pass_sym : ∀ (n : Nat) (f : val),
  {{ threadToks (GF := GF) n }} (App (Val f) (Val #())) {{ RET #(); threadToks n }}

/-- A choice correlated across pre and post (as `Begin_kv`'s `if w then wrTok γ else threadTok`). -/
axiom st_pass_ite : ∀ (w : Bool) (f : val),
  {{ if w then iprop(True) else threadTok (GF := GF) }} (App (Val f) (Val #()))
  {{ RET #(); if w then iprop(True) else threadTok }}

/-- A rule-3 finding accepted by an entry naming its key (`allow.txt`). -/
axiom st_pass_entry : ∀ (R : IProp GF) (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); R }}

/-- A rule-7 finding accepted by an entry naming its binder and type (`allow.txt`). -/
axiom st_pass_entry7 : ⊢ |==> ∃ (P : Nat → IProp GF), P 0

/-- A single mint accepted by an entry naming its count. -/
axiom st_pass_entrymint : ∀ (f : val),
  {{ (True : IProp GF) }} (App (Val f) (Val #())) {{ RET #(); threadTok }}

end AxiomTokSelftest
