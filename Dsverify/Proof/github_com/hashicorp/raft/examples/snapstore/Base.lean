/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/snapstore/Base.lean (241f27e),
with `readerSt` from the lab's `examples/inproc/Base.lean` (the `Reader` moved into snapstore).
The package fact is proved by the generated `Init.lean`.
-/
/-
(stage 3) Shared definitions of the proofs of `examples/snapstore` (an in-memory `raft.SnapshotStore`
with upstream `FileSnapshotStore`'s semantics for one retained snapshot): its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Lifting
public import Perennial.Proof.errors.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Dsverify.Proof.github_com.hashicorp.raft.Base
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Stores
public import Dsverify.Code.github_com.hashicorp.raft.examples.snapstore
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.snapstore
public import Perennial.Ghost.GhostVar

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft.examples.snapstore

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- The package-initialized state: the two error variables hold `errors.New` errors. -/
abbrev isInit : IProp GF :=
  iprop("#HErrNoSnapshot" ∷ errors.newVar ErrNoSnapshot go!"snapstore: no such snapshot" ∗
    "#HErrClosed" ∷ errors.newVar ErrClosed go!"snapstore: sink closed")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ⊢
      isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore

/-- `ErrNoSnapshot` holds a non-nil error, for good. -/
theorem errNoSnapshot_ok :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ⊢
      ∃ e : GoInterface, globalAddr ErrNoSnapshot ↦□ e ∗ ⌜e ≠ interface.nil⌝ := by
  iintro #Hi
  ihave Hi2 := isInit_access $$ Hi
  icases Hi2 with ⟨#H1, -⟩
  unfold errors.newVar
  icases H1 with ⟨%x, #Hx, -⟩
  iexists _
  iframe Hx
  ipureintro; simp

end init


/-! ## The store and its sinks (stage 3, package-internal) -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft

instance snapshotMeta_countable : Pos.Countable SnapshotMeta :=
  Pos.Countable.ofInjective
    (fun m => Pos.Countable.encode (m.Version', m.ID', m.Index', m.Term', m.Peers',
      m.Configuration'.Servers', m.ConfigurationIndex', m.Size'))
    (by
      intro a b h
      have h := Pos.encode_inj h
      obtain ⟨a1, a2, a3, a4, a5, ⟨a6⟩, a7, a8⟩ := a
      obtain ⟨b1, b2, b3, b4, b5, ⟨b6⟩, b7, b8⟩ := b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
      subst h1 h2 h3 h4 h5 h6 h7 h8; rfl)

theorem newerSnap_upd (m0 m : SnapshotMeta) (b0 b : List w8)
    (h : uint.Z m0.Term' < uint.Z m.Term' ∨ (m0.Term' = m.Term' ∧ uint.Z m0.Index' ≤ uint.Z m.Index')) :
    newerSnap (some (m0, b0)) m b = some (m, b) := by
  simp only [newerSnap]
  rw [if_pos]
  rcases h with h | ⟨h1, h2⟩
  · left; word
  · right; rw [h1]; exact ⟨rfl, by word⟩

theorem newerSnap_keep (m0 m : SnapshotMeta) (b0 b : List w8)
    (h : ¬ (uint.Z m0.Term' < uint.Z m.Term' ∨ (m0.Term' = m.Term' ∧ uint.Z m0.Index' ≤ uint.Z m.Index'))) :
    newerSnap (some (m0, b0)) m b = some (m0, b0) := by
  simp only [newerSnap]
  rw [if_neg]
  intro h'
  apply h
  rcases h' with h' | ⟨h1, h2⟩
  · left; word
  · right; refine ⟨?_, by word⟩
    have : uint.Z m0.Term' = uint.Z m.Term' := by word
    word

/-- The store's half of the latest snapshot (the client holds the other half, `isSnapStore`'s
`own`). -/
def ownLatest (γ : GName) (o : SnapLatest) : IProp GF := ghostVar γ (1 : Qp).half o

/-- The store's fields `has`, `meta`, `data` represent the latest `o` (its bytes read-only). -/
def latestCell (o : SnapLatest) (has : Bool) (mt : SnapshotMeta) (dsl : GoSlice) : IProp GF :=
  match o with
  | none => iprop(⌜has = false⌝)
  | some (m, b) => iprop(⌜has = true ∧ mt = m⌝ ∗ dsl ↦*□ b)

/-- The store's lock invariant. -/
def storeLocked (st : Loc) (γ : GName) : IProp GF :=
  iprop(∃ (o : SnapLatest) (has : Bool) (mt : SnapshotMeta) (dsl : GoSlice) (nid : w64),
    "Hg" ∷ ownLatest γ o ∗
    "Hhas" ∷ st.[Store, go!"has"] ↦ has ∗ "Hmt" ∷ st.[Store, go!"meta"] ↦ mt ∗
    "Hdat" ∷ st.[Store, go!"data"] ↦ dsl ∗ "Hnid" ∷ st.[Store, go!"nextID"] ↦ nid ∗
    "Hcell" ∷ latestCell o has mt dsl)

/-- **The store** `st` (persistent): its mutex guards `storeLocked` (the latest snapshot, half of the
ghost variable `γ`); `eof`: `io.EOF`'s value. -/
def isStore (st : Loc) (γ : GName) (eof : GoInterface) : IProp GF :=
  iprop(∃ mu : Loc, "#mu" ∷ st.[Store, go!"mu"] ↦□ mu ∗ "#Hmu" ∷ sync.isMutex mu (storeLocked st γ) ∗
    "#Heof" ∷ globalAddr io.EOF ↦□ eof)

instance isStore_persistent st γ eof : Persistent (isStore (GF := GF) st γ eof) := by
  unfold isStore; infer_instance

/-- The read-only part of the sink `k` of `Create(ver, idx, term, cfg, cfgIdx, _)` with id `id` on
the store `st` (persistent): every field of its metadata but `Size`. -/
def sinkCore (k st : Loc) (γ : GName) (eof : GoInterface) (id : GoString) (ver idx term cfgIdx : w64)
    (cfg : Configuration) : IProp GF :=
  iprop("#Hst" ∷ k.[Sink, go!"st"] ↦□ st ∗ "#Hstore" ∷ isStore st γ eof ∗
    "#Hver" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Version"] ↦□ ver ∗
    "#Hid" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"ID"] ↦□ id ∗
    "#Hidx" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Index"] ↦□ idx ∗
    "#Hterm" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Term"] ↦□ term ∗
    "#Hpeers" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Peers"] ↦□ slice.nil ∗
    "#Hcfg" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Configuration"] ↦□ cfg ∗
    "#HcfgIdx" ∷ (k.[Sink, go!"meta"]).[SnapshotMeta, go!"ConfigurationIndex"] ↦□ cfgIdx ∗
    "%Hmnn" ∷ ⌜k.[Sink, go!"meta"] ≠ null⌝)

instance sinkCore_persistent k st γ eof id ver idx term cfgIdx cfg :
    Persistent (sinkCore (GF := GF) k st γ eof id ver idx term cfgIdx cfg) := by
  unfold sinkCore; infer_instance

/-- The owner's state of the sink `k`: open with `bs` written (`some bs`), or closed (`none`). -/
def sinkSt (k : Loc) : Option (List w8) → IProp GF
  | some bs => iprop(∃ dsl : GoSlice, k.[Sink, go!"data"] ↦ dsl ∗ dsl ↦* bs ∗
      ownSliceCap w8 dsl (DFrac.own 1) ∗ k.[Sink, go!"closed"] ↦ false ∗
      (k.[Sink, go!"meta"]).[SnapshotMeta, go!"Size"] ↦ W64 0)
  | none => iprop(k.[Sink, go!"closed"] ↦ true)

/-- The commit of a sink closed with `bs` (`isSnapStore`'s `Create`), its result `R`. -/
def sinkCommit (γ : GName) (m : SnapshotMeta) (bs : List w8) (R : IProp GF) : IProp GF :=
  iprop(|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, ownLatest γ old ∗ (ownLatest γ (newerSnap old m bs) ={∅,⊤ \ ↑storeN}=∗ R))

/-- The owner's state of the sink `k` as `isSink`'s `own`: `sinkSt`, and while open the commit `Cm`
the client fixed at `Create`. -/
def sinkOwn (k : Loc) (Cm : IProp GF) : Option (List w8) → IProp GF
  | some bs => iprop(sinkSt k (some bs) ∗ Cm)
  | none => sinkSt k none

/-! ## Readers (the lab's `inproc` readers, moved into snapstore: `reader.go`) -/

/-- The state of the `*Reader` `rd` with the bytes `cs` still to come (its bytes are a read-only
copy; its offset is owned). -/
def readerSt (rd : Loc) (cs : List w8) : IProp GF :=
  iprop(∃ (sl : GoSlice) (b : List w8) (off : w64),
    rd.[Reader, go!"b"] ↦□ sl ∗ sl ↦*□ b ∗ rd.[Reader, go!"off"] ↦ off ∗
    ⌜0 ≤ sint.Z off ∧ sint.nat off ≤ b.length ∧ cs = b.drop (sint.nat off)⌝)

end defs

end github_com.hashicorp.raft.examples.snapstore

end Perennial
end
