/-
Lean-first (no Rocq counterpart).

# The Go checker's values, related to the Lean transcription (#33 S3b, 2026-11-23)

The checker's specs (`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/check/`) relate
the Go transcription's values (package `check`, translated by Goose) to the Lean transcription's
(`Tla/`, namespace `AntCheck`). Everything the checker reads is read-only once built (a stream's
events and a configuration are never written; a `State` is never written once built: an action
builds its successor from copies, `state.go`), so every predicate here is persistent (`↦□`,
`↦*□`), as tracecheck's (`Proof/.../tracecheck/etcdraft/Rep.lean`).

Strings are `GoString`s on both sides (the relation is equality). Numbers: the Lean's are `Int`,
the Go's 64-bit `int`, read signed (`sint.Z`); the stream's numbers and sizes are kept far from
overflow by `Stream.Bounded` (below `numBound`). A report's optional field is an `Option` in the
Lean and a `Has` bit in the Go (`fieldRel`): the Go's value of an absent field is unconstrained,
since the checker reads a field only after `need` finds its bit.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Tla.Check

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section types
variable [GooseExts]

/-- The Go package's types, by their short names. -/
abbrev G.Value := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value
abbrev G.Entry := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Entry
abbrev G.Msg := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg
abbrev G.SnapRef := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapRef
abbrev G.Event := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event
abbrev G.Config := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Config
abbrev G.Verdict := github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Verdict

end types

/-! ## Bounds -/

/-- The bound on the stream's numbers and on its size: a sum of three numbers below it, or of a
number and a length, stays within the Go `int` (`first + len(entries) - 1`, `prevLogIndex + k`,
`T0 + 1`; every list the checker builds is a sublist of the stream's entries put together, so no
longer than the stream's size), and as high as that allows (tracecheck's `numBound`, Q12 (a): the
closed statement's step bound, `n < 2^61`, bounds what a run reports). -/
def numBound : Int := 2 ^ 61

/-- A number of the stream within `numBound`, either sign (TLC's numbers are any 32-bit ones). -/
def numOk (x : Int) : Prop := -numBound < x ∧ x < numBound

/-- An optional number within `numBound`. -/
def optNumOk : Option Int → Prop
  | none => True
  | some x => numOk x

/-- The entries' numbers within `numBound`. -/
def entriesOk (es : List Entry) : Prop := ∀ e ∈ es, numOk e.term

/-- A reported message's numbers within `numBound`. -/
def Msg.NumsOk (m : Msg) : Prop :=
  optNumOk m.term ∧ optNumOk m.index ∧ optNumOk m.logTerm ∧ optNumOk m.commit ∧
  ∀ es, m.entries = some es → entriesOk es

/-- The entries a message carries (0 if it has none). -/
def Msg.size (m : Msg) : Nat := (m.entries.getD []).length

/-- A report's numbers within `numBound`. -/
def Event.NumsOk (ev : Event) : Prop :=
  optNumOk ev.term ∧ optNumOk ev.commit ∧ optNumOk ev.first ∧ optNumOk ev.lastIndex ∧
  optNumOk ev.lastTerm ∧ optNumOk ev.applied ∧ optNumOk ev.w ∧ optNumOk ev.more ∧
  optNumOk ev.index ∧ (∀ s, ev.snap = some s → numOk s.index ∧ numOk s.term) ∧
  (∀ es, ev.entries = some es → entriesOk es) ∧ (∀ m, ev.msg = some m → m.NumsOk) ∧
  (∀ ms, ev.cause = some ms → ∀ m ∈ ms, m.NumsOk)

/-- A report's size: its entries, its messages' entries, its lists of names and messages. -/
def Event.size (ev : Event) : Nat :=
  (ev.entries.getD []).length + (ev.msg.map Msg.size).getD 0 +
  ((ev.cause.getD []).map Msg.size).sum + (ev.cause.getD []).length +
  (ev.voters.getD []).length + (ev.outgoing.getD []).length

/-- **The stream's numbers and size within `numBound`** (`Run`'s premise for the Go `int`): every
number of every report, and the number of reports plus their sizes. -/
def Stream.Bounded (evs : List Event) : Prop :=
  ((evs.length + (evs.map Event.size).sum : Nat) : Int) < numBound ∧ ∀ ev ∈ evs, ev.NumsOk

/-- The configuration's sets within `numBound` (`Majority`'s `Cardinality(...) * 2`). -/
def Config.Bounded (cfg : Config) : Prop :=
  (cfg.server.length : Int) < numBound ∧ (cfg.initVoters.length : Int) < numBound

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-! ## Optional fields -/

/-- `bit` is set in `has` (Go: `Has&bit != 0`). -/
def hasBit (has bit : w32) : Prop := (has &&& bit) ≠ W32 0

/-- A report's optional field: absent, its bit clear; present, its bit set and the Go value
`rel`-related to the Lean's. -/
def fieldRel {α β : Type} (has bit : w32) (rel : α → β → Prop) (g : α) : Option β → Prop
  | none => ¬ hasBit has bit
  | some b => hasBit has bit ∧ rel g b

/-- `fieldRel` for a field compared by `=` (a string, a boolean). -/
abbrev fieldIs {α : Type} (has bit : w32) (g : α) (o : Option α) : Prop := fieldRel has bit (· = ·) g o

/-- `fieldRel` for an `int` field. -/
abbrev fieldZ (has bit : w32) (g : w64) (o : Option Int) : Prop :=
  fieldRel has bit (fun g x => sint.Z g = x) g o

/-- An optional field held in memory (a slice): absent, its bit clear; present, its bit set and
`rep` of the Go value. -/
def fieldRO {α β : Type} (has bit : w32) (rep : α → β → IProp GF) (g : α) : Option β → IProp GF
  | none => iprop(⌜¬ hasBit has bit⌝)
  | some b => iprop(⌜hasBit has bit⌝ ∗ rep g b)

/-! ## Strings, values, entries, messages -/

/-- A Go `[]string` (a `Set` among them) holding `xs`. -/
def strsRO (sl : GoSlice) (xs : List Str) : IProp GF := iprop(sl ↦*□ xs)

/-- A Go `Value` holding `w`. -/
def valueRO (v : G.Value) (w : Value) : IProp GF :=
  iprop(⌜v.IsRec' = w.isRec ∧ v.Str' = w.str ∧ v.Joint' = w.joint ∧ v.Leave' = w.leave⌝ ∗
    strsRO v.Add' w.add ∗ strsRO v.Remove' w.remove)

/-- A Go `Entry` holding `x`. -/
def entryRO (e : G.Entry) (x : Entry) : IProp GF :=
  iprop(⌜sint.Z e.Term' = x.term ∧ e.Type' = x.type⌝ ∗ valueRO e.Value' x.value)

/-- A Go `[]Entry` holding `l`. -/
def logRO (sl : GoSlice) (l : List Entry) : IProp GF :=
  iprop(∃ es : List G.Entry, sl ↦*□ es ∗ [∗list] e;x ∈ es;l, entryRO e x)

/-- The bits of `Msg.Has` (`event.go`'s `MF*`). -/
def mfType : w32 := W32 1
def mfFrom : w32 := W32 2
def mfTo : w32 := W32 4
def mfTerm : w32 := W32 8
def mfIndex : w32 := W32 16
def mfLogTerm : w32 := W32 32
def mfEntries : w32 := W32 64
def mfCommit : w32 := W32 128
def mfReject : w32 := W32 256

/-- A Go `Msg` (a value) holding `m`. -/
def msgRO (g : G.Msg) (m : Msg) : IProp GF :=
  iprop(⌜fieldIs g.Has' mfType g.Type' m.type ∧ fieldIs g.Has' mfFrom g.From' m.frm ∧
      fieldIs g.Has' mfTo g.To' m.to ∧ fieldZ g.Has' mfTerm g.Term' m.term ∧
      fieldZ g.Has' mfIndex g.Index' m.index ∧ fieldZ g.Has' mfLogTerm g.LogTerm' m.logTerm ∧
      fieldZ g.Has' mfCommit g.Commit' m.commit ∧ fieldIs g.Has' mfReject g.Reject' m.reject⌝ ∗
    fieldRO g.Has' mfEntries logRO g.Entries' m.entries)

/-- A Go `[]Msg` holding `ms`. -/
def msgsRO (sl : GoSlice) (ms : List Msg) : IProp GF :=
  iprop(∃ gs : List G.Msg, sl ↦*□ gs ∗ [∗list] g;m ∈ gs;ms, msgRO g m)

/-! ## Reports and the configuration -/

/-- The bits of `Event.Has` (`event.go`'s `F*`). -/
def fBy : w32 := W32 1
def fRole : w32 := W32 2
def fTerm : w32 := W32 4
def fVote : w32 := W32 8
def fCommit : w32 := W32 16
def fFirst : w32 := W32 32
def fEntries : w32 := W32 64
def fLastIndex : w32 := W32 128
def fLastTerm : w32 := W32 256
def fApplied : w32 := W32 512
def fVoters : w32 := W32 1024
def fOutgoing : w32 := W32 2048
def fSnap : w32 := W32 4096
def fMsg : w32 := W32 8192
def fCause : w32 := W32 16384
def fB : w32 := W32 32768
def fA : w32 := W32 65536
def fW : w32 := W32 131072
def fMore : w32 := W32 262144
def fIndex : w32 := W32 524288
def fCtx : w32 := W32 1048576

/-- A Go `SnapRef` holding `s`. -/
def snapRel (g : G.SnapRef) (s : SnapRef) : Prop := sint.Z g.Index' = s.index ∧ sint.Z g.Term' = s.term

/-- A Go `*Event` holding `ev`. -/
def eventRO (p : Loc) (ev : Event) : IProp GF :=
  iprop(∃ g : G.Event, p ↦□ g ∗
    ⌜g.E' = ev.e ∧ g.Node' = ev.node ∧ g.Bad' = ev.bad ∧
      (hasBit g.Has' fB ↔ ev.b = true) ∧ (hasBit g.Has' fA ↔ ev.a = true) ∧
      fieldIs g.Has' fBy g.By' ev.byE ∧ fieldIs g.Has' fRole g.Role' ev.role ∧
      fieldZ g.Has' fTerm g.Term' ev.term ∧ fieldIs g.Has' fVote g.Vote' ev.vote ∧
      fieldZ g.Has' fCommit g.Commit' ev.commit ∧ fieldZ g.Has' fFirst g.First' ev.first ∧
      fieldZ g.Has' fLastIndex g.LastIdx' ev.lastIndex ∧ fieldZ g.Has' fLastTerm g.LastTerm' ev.lastTerm ∧
      fieldZ g.Has' fApplied g.Applied' ev.applied ∧ fieldRel g.Has' fSnap snapRel g.Snap' ev.snap ∧
      fieldZ g.Has' fW g.W' ev.w ∧ fieldZ g.Has' fMore g.More' ev.more ∧
      fieldZ g.Has' fIndex g.Index' ev.index ∧ fieldIs g.Has' fCtx g.Ctx' ev.ctx⌝ ∗
    fieldRO g.Has' fEntries logRO g.Entries' ev.entries ∗
    fieldRO g.Has' fVoters strsRO g.Voters' ev.voters ∗
    fieldRO g.Has' fOutgoing strsRO g.Outgoing' ev.outgoing ∗
    fieldRO g.Has' fMsg msgRO g.Msg' ev.msg ∗
    fieldRO g.Has' fCause msgsRO g.Cause' ev.cause)

/-- A Go `[]*Event` holding the stream `evs`. -/
def eventsRO (sl : GoSlice) (evs : List Event) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ [∗list] p;ev ∈ ps;evs, eventRO p ev)

/-- A Go `*Config` holding `cfg`. -/
def configRO (p : Loc) (cfg : Config) : IProp GF :=
  iprop(∃ g : G.Config, p ↦□ g ∗ strsRO g.Server' cfg.server ∗ strsRO g.InitVoters' cfg.initVoters ∗
    ⌜g.Bootstrapped' = cfg.bootstrapped⌝)

/-! ## Verdicts -/

/-- The Go `Kind` of a verdict's kind (`Accepted` .. `Error`, `iota`'s). -/
def kindW : Kind → w64
  | .accepted => W64 0 | .rejected => W64 1 | .violated => W64 2 | .error => W64 3

/-- A Go `Verdict` holding `v` (`Err` empty: `Run` never sets it). -/
def verdictRO (r : G.Verdict) (v : Verdict) : IProp GF :=
  iprop(⌜r.Kind' = kindW v.kind ∧ sint.Z r.K' = v.k ∧ r.Err' = []⌝ ∗ strsRO r.Names' v.names)

/-! ## Persistence -/

instance fieldRO_persistent {α β : Type} (has bit : w32) (rep : α → β → IProp GF)
    [∀ a b, Persistent (rep a b)] (g : α) (o : Option β) : Persistent (fieldRO has bit rep g o) := by
  cases o <;> unfold fieldRO <;> infer_instance

instance strsRO_persistent (sl : GoSlice) (xs : List Str) : Persistent (strsRO (GF := GF) sl xs) := by
  unfold strsRO; infer_instance

instance valueRO_persistent (v : G.Value) (w : Value) : Persistent (valueRO (GF := GF) v w) := by
  unfold valueRO; infer_instance

instance entryRO_persistent (e : G.Entry) (x : Entry) : Persistent (entryRO (GF := GF) e x) := by
  unfold entryRO; infer_instance

instance logRO_persistent (sl : GoSlice) (l : List Entry) : Persistent (logRO (GF := GF) sl l) := by
  unfold logRO; infer_instance

instance msgRO_persistent (g : G.Msg) (m : Msg) : Persistent (msgRO (GF := GF) g m) := by
  unfold msgRO; infer_instance

instance msgsRO_persistent (sl : GoSlice) (ms : List Msg) : Persistent (msgsRO (GF := GF) sl ms) := by
  unfold msgsRO; infer_instance

instance eventRO_persistent (p : Loc) (ev : Event) : Persistent (eventRO (GF := GF) p ev) := by
  unfold eventRO; infer_instance

instance eventsRO_persistent (sl : GoSlice) (evs : List Event) : Persistent (eventsRO (GF := GF) sl evs) := by
  unfold eventsRO; infer_instance

instance configRO_persistent (p : Loc) (cfg : Config) : Persistent (configRO (GF := GF) p cfg) := by
  unfold configRO; infer_instance

instance verdictRO_persistent (r : G.Verdict) (v : Verdict) : Persistent (verdictRO (GF := GF) r v) := by
  unfold verdictRO; infer_instance

/-! ## Sub-slices -/

/-- A big separating conjunction over two lists of the same length holds over their sublists
`[lo, hi)` (a copy of tracecheck's `Etcdraft.bigSepL2_subslice`, a candidate for Perennial). -/
theorem bigSepL2_subslice {A B : Type} (Φ : A → B → IProp GF) (l1 : List A) (l2 : List B)
    (lo hi : Nat) (hlen : l1.length = l2.length) :
    ([∗list] x;y ∈ l1;l2, Φ x y) ⊢ [∗list] x;y ∈ subslice lo hi l1;subslice lo hi l2, Φ x y := by
  conv => lhs; rw [← List.take_append_drop hi l1, ← List.take_append_drop hi l2]
  refine (BigSepL2.bigSepL2_append (Or.inl (by simp [hlen]))).1.trans (sep_elim_left.trans ?_)
  unfold subslice
  conv => lhs; rw [← List.take_append_drop lo (l1.take hi), ← List.take_append_drop lo (l2.take hi)]
  exact (BigSepL2.bigSepL2_append (Or.inl (by simp [hlen]))).1.trans sep_elim_right

/-- A log's sub-slice `sl[lo:hi]` holds the log's elements `[lo, hi)`. -/
theorem logRO_subslice (sl : GoSlice) (l : List Entry) (lo hi : w64)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z sl.len) :
    logRO (GF := GF) sl l ⊢
      logRO (slice.slice sl G.Entry lo hi) (subslice (sint.nat lo) (sint.nat hi) l) := by
  unfold logRO
  iintro ⟨%es, #Hes, #Hb⟩
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  icases (ownSlice_slice lo hi sl _ es hb).1 $$ Hes with ⟨-, #H2, -⟩
  iexists (subslice (sint.nat lo) (sint.nat hi) es)
  isplitr
  · iexact H2
  iapply bigSepL2_subslice (fun e x => entryRO (GF := GF) e x) es l _ _ Hl
  iexact Hb

end defs

end AntCheck
end EtcdGrove
end Perennial
