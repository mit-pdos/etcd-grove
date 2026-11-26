/-
The client's committed data (U0a of `notes/bbolt-proof-plan.md`; design §3.3): `boltStateDef`,
what `boltState` is sealed to, and its laws restated over it.

The client holds half of `st` (at its fraction `q`) and `bq` at `q` (for validity); the library
holds the other half (¼ `metaR`, ¼ `rwR`/the writer), always the data of the committed state and
its version (the committed txid, `boltStateVDef`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Names
public import GeneratedProof.go_etcd_io.bbolt
public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoNat
public import Iris.BI.Lib.Atomic
public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode

section state
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The crash part (W3 of `plans/bbolt-crash-plan.md`) -/

/-- **The crash invariant's client names**, `none` outside crash mode (persistent: `B.cn`'s discarded
value, `bMode` records it). -/
def cnReg (B : BNs) (o : Option CsG) : IProp GF := dghostVar B.cn DFrac.discard o

/-- A version's committed data (persistent): the crash invariant's history's element. -/
def histE (g : CsG) (k : Nat) (D : Data) : IProp GF := iprop(k ↪[g.hs]□ D)

/-- The version `k` finished its commit's second `fdatasync` (persistent): the synced mark's lower
bound. -/
def syncedE (g : CsG) (k : Nat) : IProp GF := monoNatLbOwn g.sy k

/-- **The committed data's crash part at the names `o`**, at fraction `q`: in crash mode the version
variable at `q`'s half (the crash invariant's client resource `bR` holds the other half of all of
it, so the two agree: the invariant's value is at the committed state) and the history's element of
the version; outside crash mode nothing. -/
def cpart (o : Option CsG) (q : Qp) (D : Data) (ν : Nat) : IProp GF :=
  match o with
  | none => iprop(emp)
  | some g => iprop(ghostVar g.cv q.half (D, ν) ∗ histE g ν D)

/-- **The committed data's crash part** (`cpart` at the registered names). -/
def crashPart (B : BNs) (q : Qp) (D : Data) (ν : Nat) : IProp GF :=
  iprop(∃ o : Option CsG, cnReg B o ∗ cpart o q D ν)

instance cnReg_persistent (B : BNs) (o : Option CsG) : Persistent (cnReg (GF := GF) B o) := by
  unfold cnReg; infer_instance

instance histE_persistent (g : CsG) (k : Nat) (D : Data) : Persistent (histE (GF := GF) g k D) := by
  unfold histE; infer_instance

instance syncedE_persistent (g : CsG) (k : Nat) : Persistent (syncedE (GF := GF) g k) := by
  unfold syncedE; infer_instance

instance cpart_timeless (o : Option CsG) (q : Qp) (D : Data) (ν : Nat) :
    Timeless (cpart (GF := GF) o q D ν) := by
  unfold cpart histE; cases o <;> dsimp only <;> infer_instance

instance crashPart_timeless (B : BNs) (q : Qp) (D : Data) (ν : Nat) :
    Timeless (crashPart (GF := GF) B q D ν) := by
  unfold crashPart cnReg; infer_instance

theorem cpart_some (g : CsG) (q : Qp) (D : Data) (ν : Nat) :
    cpart (GF := GF) (some g) q D ν ⊣⊢ ghostVar g.cv q.half (D, ν) ∗ histE g ν D := .rfl

theorem cnReg_agree (B : BNs) (o1 o2 : Option CsG) :
    cnReg (GF := GF) B o1 ∗ cnReg B o2 ⊢ ⌜o1 = o2⌝ := by
  unfold cnReg
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.2

theorem cpart_fractional (o : Option CsG) (D : Data) (ν : Nat) :
    Fractional (fun q => cpart (GF := GF) o q D ν) := by
  unfold cpart
  cases o with
  | none => dsimp only; exact ⟨fun _ _ => emp_sep.symm⟩
  | some g =>
    dsimp only
    have h1 := ghostVar_half_fractional (GF := GF) g.cv (D, ν)
    refine ⟨fun p q => ⟨?_, ?_⟩⟩
    · iintro ⟨Hv, #He⟩
      icases (h1.fractional p q).1 $$ Hv with ⟨H1, H2⟩
      iframe; iframe #
    · iintro ⟨⟨H1, #He⟩, ⟨H2, -⟩⟩
      iframe He
      iapply (h1.fractional p q).2; iframe

theorem crashPart_fractional (B : BNs) (D : Data) (ν : Nat) :
    Fractional (fun q => crashPart (GF := GF) B q D ν) := by
  unfold crashPart
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%o, #Hr, Hc⟩
    icases ((cpart_fractional (GF := GF) o D ν).fractional p q).1 $$ Hc with ⟨H1, H2⟩
    isplitl [H1]
    · iexists o; iframe; iframe #
    · iexists o; iframe; iframe #
  · iintro ⟨⟨%o1, #Hr1, H1⟩, ⟨%o2, #Hr2, H2⟩⟩
    ihave %ho := cnReg_agree B o1 o2 $$ [Hr1 Hr2]
    · iframe #
    subst ho
    iexists o1
    iframe Hr1
    iapply ((cpart_fractional (GF := GF) o1 D ν).fractional p q).2; iframe

/-- **The committed data is `D` at version `ν`**, at fraction `q` (`boltStateV γ q D ν`, with
`B = bnsOf γ.gs`): the version is the committed state's txid (`metaR`'s and the writer's quarters
hold `(treeData C, C.txid)`), so it moves by exactly one at each commit point; with the crash part
(W3: in crash mode the version variable the crash invariant's client resource agrees with, and the
history's element of the version). -/
def boltStateVDef (B : BNs) (q : Qp) (D : Data) (ν : Nat) : IProp GF :=
  iprop(ghostVar B.st q.half (D, ν) ∗ ghostVar B.bq q () ∗ crashPart B q D ν)

/-- **The committed data is `D`**, at fraction `q` (`boltState γ q D`, with `B = bnsOf γ.gs`), at
some version. -/
def boltStateDef (B : BNs) (q : Qp) (D : Data) : IProp GF :=
  iprop(∃ ν : Nat, boltStateVDef B q D ν)

instance boltStateVDef_timeless (B : BNs) (q : Qp) (D : Data) (ν : Nat) :
    Timeless (boltStateVDef (GF := GF) B q D ν) := by
  unfold boltStateVDef; infer_instance

instance boltStateDef_timeless (B : BNs) (q : Qp) (D : Data) :
    Timeless (boltStateDef (GF := GF) B q D) := by
  unfold boltStateDef; infer_instance

theorem boltStateVDef_fractional (B : BNs) (D : Data) (ν : Nat) :
    Fractional (fun q => boltStateVDef (GF := GF) B q D ν) := by
  unfold boltStateVDef
  have h1 := ghostVar_half_fractional (GF := GF) B.st (D, ν)
  have h2 := ghostVar_fractional (GF := GF) B.bq ()
  have h3 := crashPart_fractional (GF := GF) B D ν
  exact ⟨fun p q => (sep_congr (h1.fractional p q)
    ((sep_congr (h2.fractional p q) (h3.fractional p q)).trans sep_sep_sep_comm)).trans
    sep_sep_sep_comm⟩

theorem boltStateVDef_agree (B : BNs) (q1 q2 : Qp) (D1 D2 : Data) (ν1 ν2 : Nat) :
    boltStateVDef (GF := GF) B q1 D1 ν1 ∗ boltStateVDef B q2 D2 ν2 ⊢ ⌜D1 = D2 ∧ ν1 = ν2⌝ := by
  unfold boltStateVDef
  iintro ⟨⟨H1, -⟩, H2, -⟩
  icombine H1 H2 gives %h
  ipureintro; exact Prod.mk.inj h.2

theorem boltStateDef_fractional (B : BNs) (D : Data) :
    Fractional (fun q => boltStateDef (GF := GF) B q D) := by
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · unfold boltStateDef
    iintro ⟨%ν, H⟩
    icases ((boltStateVDef_fractional (GF := GF) B D ν).fractional p q).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists ν; iexact H1
    · iexists ν; iexact H2
  · unfold boltStateDef
    iintro ⟨⟨%ν1, H1⟩, ⟨%ν2, H2⟩⟩
    ihave %h := boltStateVDef_agree B p q D D ν1 ν2 $$ [H1 H2]
    · iframe
    obtain ⟨-, rfl⟩ := h
    iexists ν1
    iapply ((boltStateVDef_fractional (GF := GF) B D ν1).fractional p q).2
    iframe

theorem boltStateDef_agree (B : BNs) (q1 q2 : Qp) (D1 D2 : Data) :
    boltStateDef (GF := GF) B q1 D1 ∗ boltStateDef B q2 D2 ⊢ ⌜D1 = D2⌝ := by
  unfold boltStateDef
  iintro ⟨⟨%ν1, H1⟩, ⟨%ν2, H2⟩⟩
  ihave %h := boltStateVDef_agree B q1 q2 D1 D2 ν1 ν2 $$ [H1 H2]
  · iframe
  ipureintro; exact h.1

theorem boltStateVDef_valid (B : BNs) (q : Qp) (D : Data) (ν : Nat) :
    boltStateVDef (GF := GF) B q D ν ⊢ ⌜q ≤ 1⌝ := by
  unfold boltStateVDef
  iintro ⟨-, H, -⟩
  ihave ⟨H1, H2⟩ := (ghostVar_split_half B.bq q ()).1 $$ H
  icombine H1 H2 gives %h
  ipureintro; rw [Qp.half_add_half] at h; exact h.1

theorem boltStateDef_valid (B : BNs) (q : Qp) (D : Data) :
    boltStateDef (GF := GF) B q D ⊢ ⌜q ≤ 1⌝ := by
  unfold boltStateDef
  iintro ⟨%ν, H⟩
  iapply boltStateVDef_valid $$ H

/-- The library's quarter agrees with the client's data and version (any fraction). -/
theorem boltStateVDef_agree_lib (B : BNs) (q : Qp) (D D' : Data) (ν ν' : Nat) :
    boltStateVDef (GF := GF) B q D ν ∗ ghostVar B.st (1 : Qp).half.half (D', ν') ⊢
      ⌜D = D' ∧ ν = ν'⌝ := by
  unfold boltStateVDef
  iintro ⟨⟨H1, -⟩, H2⟩
  icombine H1 H2 gives %h
  ipureintro; exact Prod.mk.inj h.2

/-- The library's quarter agrees with the client's data (any fraction). Used by U10 (the commit
point opens the AU) and U5 (`Begin`'s AUs, `boltTx_base`). -/
theorem boltStateDef_agree_lib (B : BNs) (q : Qp) (D D' : Data) (ν' : Nat) :
    boltStateDef (GF := GF) B q D ∗ ghostVar B.st (1 : Qp).half.half (D', ν') ⊢ ⌜D = D'⌝ := by
  unfold boltStateDef
  iintro ⟨⟨%ν, H1⟩, H2⟩
  ihave %h := boltStateVDef_agree_lib B q D D' ν ν' $$ [H1 H2]
  · iframe
  ipureintro; exact h.1

/-- `boltState_read_au` over the definition. -/
theorem boltState_read_au' (B : BNs) (N : Namespace) (D : Data) :
    boltStateDef (GF := GF) B 1 D ⊢
      AU <{ ∃∃ (q : Qp) (D' : Data), boltStateDef B q D' }> @ ⊤ \ ↑N, ∅
        <{ boltStateDef B q D', COMM boltStateDef B 1 D ∗ ⌜D' = D⌝ }> := by
  iintro H
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists 1, D
  iframe H
  isplit
  · iintro H; imod Hcl with -; imodintro; iexact H
  · iintro H; imod Hcl with -; imodintro; iframe H; ipureintro; rfl

/-- `boltState_commit_au` over the definition: the versioned commit update, at the version of the
client's state. -/
theorem boltState_commit_au' (B : BNs) (N : Namespace) (D S : Data) :
    boltStateDef (GF := GF) B 1 D ⊢
      AU <{ ∃∃ (D' : Data) (ν' : Nat), boltStateVDef B 1 D' ν' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = D⌝ ∗ boltStateVDef B 1 S (ν' + 1), COMM boltStateDef B 1 S }> := by
  unfold boltStateDef
  iintro ⟨%ν, H⟩
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists D, ν
  iframe H
  isplit
  · iintro H; imod Hcl with -; imodintro; iexact H
  · iintro ⟨-, H⟩; imod Hcl with -; imodintro; iexists (ν + 1); iexact H

/-- **A commit update over the data alone is one over the versioned state** (the client-side
conversion: a caller holding `boltState`'s update gives `Tx.Commit` the versioned one). -/
theorem commitAU_versioned (B : BNs) (N : Namespace) (Db Dn : Data) (Q : IProp GF) :
    AU <{ ∃∃ (D' : Data), boltStateDef B 1 D' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = Db⌝ ∗ boltStateDef B 1 Dn, COMM Q }> ⊢
      AU <{ ∃∃ (D' : Data) (ν : Nat), boltStateVDef B 1 D' ν }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = Db⌝ ∗ boltStateVDef B 1 Dn (ν + 1), COMM Q }> := by
  iintro Hau
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%D', Hx, Hcl⟩
  unfold boltStateDef
  icases Hx with ⟨%ν, Hx⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists D', ν
  iframe Hx
  isplit
  · iintro Hx
    icases Hcl with ⟨Hab, -⟩
    iapply Hab
    iexists ν; iexact Hx
  · iintro ⟨%hD, Hx⟩
    icases Hcl with ⟨-, Hco⟩
    iapply Hco
    isplitr
    · ipureintro; exact hD
    iexists (ν + 1); iexact Hx

end state

end bbolt
end EtcdGrove
end Perennial
