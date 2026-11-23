/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ConnSlots.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The peers' slots of `ConnectToPeers` (`Peers`, `PeerReaders`, `PeerWriters`, `Alive`), split into
their elements for the dial loop and `waitForPeerConnections`, and put back.

* `replica.slotE`: the four elements of index `i`.
* `replica.slots_open`: the four slices of `New` (nothing connected) are the slots of every
  index, each empty, and a wand that puts back any slots.
* `replica.range_split3`: the indices `range N` are those below `m`, `m`, those above.
* `replica.slots_close`: the peers' slots (`replica.peerSlot`) of every index give the four
  slices back, each peer's reader (for its listener) and writer (for `r.M`'s invariant).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.SliceElems

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open BigSepL

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section slots
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- The four elements of index `i`. -/
def replica.slotE (pssl prsl pwsl alsl : GoSlice) (i : Nat) (x : GoInterface × Loc × Loc × Bool) :
    IProp netDistGF :=
  iprop(replica.elem pssl i x.1 ∗ replica.elem prsl i x.2.1 ∗ replica.elem pwsl i x.2.2.1 ∗
    replica.elem alsl i x.2.2.2)

/-- An empty slot, as `waitForPeerConnections` takes it. -/
def replica.emptySlot (pssl prsl pwsl alsl : GoSlice) (i : Nat) : IProp netDistGF :=
  iprop(∃ (cv : GoInterface) (rd w : Loc) (al : Bool), replica.elem pssl i cv ∗
    replica.elem prsl i rd ∗ replica.elem pwsl i w ∗ replica.elem alsl i al ∗
    ⌜rd = null ∧ w = null⌝)

theorem replica.elems_range {V : Type} [ZeroVal V] [TypedPointsto (GF := netDistGF) V]
    (s : GoSlice) (N : Nat) (x : V) :
    (s ↦* List.replicate N x : IProp netDistGF) ⊢
      ([∗list] j ∈ List.range N, replica.elem s j x) ∗
      (∀ vs' : List V, ⌜vs'.length = N⌝ -∗
        ([∗list] i ↦ v ∈ vs', replica.elem s i v) -∗ s ↦* vs') := by
  iintro Hs
  icases ownSlice_elems_acc s (DFrac.own 1) (List.replicate N x) $$ Hs with ⟨Hel, Hb⟩
  isplitl [Hel]
  · iapply (bigSepL_range_idx (fun j => replica.elem s j x) N).1
    iapply (bigSepL_replicate_range (fun (i : Nat) (v : V) => replica.elem s i v) x N).1
    iexact Hel
  · iintro %vs' %Hl Hel
    iapply Hb $$ %vs'
    · ipureintro; simp [Hl]
    · iexact Hel

theorem replica.bigSepL_sep4 (l : List Nat) (A B C D : Nat → IProp netDistGF) :
    (([∗list] j ∈ l, A j) ∗ ([∗list] j ∈ l, B j) ∗ ([∗list] j ∈ l, C j) ∗
      ([∗list] j ∈ l, D j) : IProp netDistGF) ⊢ [∗list] j ∈ l, A j ∗ B j ∗ C j ∗ D j := by
  refine (sep_mono_right (sep_mono_right
    (bigSepL_sep_eqv (Φ := fun _ j => C j) (Ψ := fun _ j => D j)).2)).trans ?_
  refine (sep_mono_right
    (bigSepL_sep_eqv (Φ := fun _ j => B j) (Ψ := fun _ j => iprop(C j ∗ D j))).2).trans ?_
  exact (bigSepL_sep_eqv (Φ := fun _ j => A j) (Ψ := fun _ j => iprop(B j ∗ C j ∗ D j))).2

theorem replica.slots_open (N : Nat) (pssl prsl pwsl alsl : GoSlice) :
    (pssl ↦* List.replicate N (interface.nil : GoInterface) ∗
      prsl ↦* List.replicate N (null : Loc) ∗ pwsl ↦* List.replicate N (null : Loc) ∗
      alsl ↦* List.replicate N false : IProp netDistGF) ⊢
      ([∗list] j ∈ List.range N, replica.emptySlot pssl prsl pwsl alsl j) ∗
      (∀ xs : List (GoInterface × Loc × Loc × Bool), ⌜xs.length = N⌝ -∗
        ([∗list] i ↦ x ∈ xs, replica.slotE pssl prsl pwsl alsl i x) -∗
        pssl ↦* xs.map (·.1) ∗ prsl ↦* xs.map (·.2.1) ∗ pwsl ↦* xs.map (·.2.2.1) ∗
        alsl ↦* xs.map (·.2.2.2)) := by
  iintro ⟨H1, H2, H3, H4⟩
  icases replica.elems_range pssl N _ $$ H1 with ⟨E1, B1⟩
  icases replica.elems_range prsl N _ $$ H2 with ⟨E2, B2⟩
  icases replica.elems_range pwsl N _ $$ H3 with ⟨E3, B3⟩
  icases replica.elems_range alsl N _ $$ H4 with ⟨E4, B4⟩
  isplitl [E1 E2 E3 E4]
  · ihave E := (replica.bigSepL_sep4 (List.range N) (fun j => replica.elem pssl j _)
        (fun j => replica.elem prsl j _) (fun j => replica.elem pwsl j _)
        (fun j => replica.elem alsl j _)) $$ [E1 E2 E3 E4]
    · iframe
    iapply bigSepL_mono _ $$ E
    iintro %k %j %_ ⟨A, B, C, D⟩
    unfold replica.emptySlot
    iexists _, _, _, _
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · iintro %xs %Hl Hxs
    unfold replica.slotE
    icases bigSepL_sep_eqv.1 $$ Hxs with ⟨X1, Hxs⟩
    icases bigSepL_sep_eqv.1 $$ Hxs with ⟨X2, Hxs⟩
    icases bigSepL_sep_eqv.1 $$ Hxs with ⟨X3, X4⟩
    isplitl [B1 X1]
    · iapply B1 $$ %(xs.map (fun x : GoInterface × Loc × Loc × Bool => x.1))
      · ipureintro; simp [Hl]
      · rw [bigSepL_map]; iexact X1
    isplitl [B2 X2]
    · iapply B2 $$ %(xs.map (fun x : GoInterface × Loc × Loc × Bool => x.2.1))
      · ipureintro; simp [Hl]
      · rw [bigSepL_map]; iexact X2
    isplitl [B3 X3]
    · iapply B3 $$ %(xs.map (fun x : GoInterface × Loc × Loc × Bool => x.2.2.1))
      · ipureintro; simp [Hl]
      · rw [bigSepL_map]; iexact X3
    · iapply B4 $$ %(xs.map (fun x : GoInterface × Loc × Loc × Bool => x.2.2.2))
      · ipureintro; simp [Hl]
      · rw [bigSepL_map]; iexact X4

theorem replica.range_split3 (Φ : Nat → IProp netDistGF) (N m : Nat) (hm : m < N) :
    ([∗list] j ∈ List.range N, Φ j) ⊣⊢
      ([∗list] j ∈ List.range m, Φ j) ∗ Φ m ∗
        [∗list] j ∈ List.range' (m + 1) (N - (m + 1)), Φ j := by
  have e : List.range N = List.range m ++ m :: List.range' (m + 1) (N - (m + 1)) := by
    rw [List.range_eq_range', List.range_eq_range']
    have h1 : N = m + ((N - (m + 1)) + 1) := by omega
    rw [show List.range' 0 N = List.range' 0 (m + ((N - (m + 1)) + 1)) by rw [← h1]]
    rw [← List.range'_append]
    simp only [List.range'_succ, Nat.zero_add, Nat.one_mul]
  rw [e]
  refine bigSepL_append.trans ?_
  exact ⟨sep_mono .rfl (bigSepL_cons (Φ := fun _ j => Φ j)).1,
    sep_mono .rfl (bigSepL_cons (Φ := fun _ j => Φ j)).2⟩

/-- A peer's reader, as its listener takes it (none for a null reader). -/
def replica.readerPart (γ : sp.Names) (γc γm : GName) (me : w32) (i : Nat) (rd : Loc) :
    IProp netDistGF :=
  iprop(⌜rd = null⌝ ∨ ∃ (cv : GoInterface) (cid : w64) (R : List w8),
    net.rpc.connIface cv cid (sp.peerRdKind me i).side ∗ sp.connKind γ cid .peer ∗
    bufio.ownReader rd cv
      (recvTok cid (sp.peerRdKind me i).side ((sp.peerRdKind me i).proto γ γc γm)) R ∗
    ⌜sp.rdAt (sp.peerRdKind me i) [] R⌝)

/-- A peer's writer, as `r.M`'s invariant holds it. -/
def replica.writerPart (γ : sp.Names) (γc γm : GName) (me : w32) (i : Nat) (w : Loc) :
    IProp netDistGF :=
  iprop(⌜w = null⌝ ∨ sp.wrSt γ γc γm w (sp.peerWrKind me i))

theorem replica.slots_close (γ : sp.Names) (γc γm : GName) (me : w32) (N : Nat)
    (pssl prsl pwsl alsl : GoSlice) :
    ([∗list] j ∈ List.range N, replica.peerSlot γ γc γm me pssl prsl pwsl alsl j) ∗
    (∀ xs : List (GoInterface × Loc × Loc × Bool), ⌜xs.length = N⌝ -∗
        ([∗list] i ↦ x ∈ xs, replica.slotE pssl prsl pwsl alsl i x) -∗
        pssl ↦* xs.map (·.1) ∗ prsl ↦* xs.map (·.2.1) ∗ pwsl ↦* xs.map (·.2.2.1) ∗
        alsl ↦* xs.map (·.2.2.2)) ⊢
      ∃ (cvs : List GoInterface) (rds pws : List Loc) (als : List Bool),
        pssl ↦* cvs ∗ prsl ↦* rds ∗ pwsl ↦* pws ∗ alsl ↦* als ∗
        ⌜cvs.length = N ∧ rds.length = N ∧ pws.length = N ∧ als.length = N⌝ ∗
        ([∗list] i ↦ rd ∈ rds, replica.readerPart γ γc γm me i rd) ∗
        ([∗list] i ↦ w ∈ pws, replica.writerPart γ γc γm me i w) := by
  iintro ⟨Hs, Hb⟩
  ihave Hs : ([∗list] j ∈ List.range N, ∃ x : GoInterface × Loc × Loc × Bool,
      replica.slotE pssl prsl pwsl alsl j x ∗
      (replica.readerPart γ γc γm me j x.2.1 ∗ replica.writerPart γ γc γm me j x.2.2.1)) $$ [Hs]
  · iapply bigSepL_mono _ $$ Hs
    iintro %k %j %_ Hj
    unfold replica.peerSlot
    icases Hj with ⟨%cv, %rd, %w, %al, A, B, C, D, Hc⟩
    iexists (cv, rd, w, al)
    unfold replica.slotE
    iframe A B C D
    unfold replica.readerPart replica.writerPart
    icases Hc with (%Hn | ⟨%cid, %R, #Hci, #Hk, Hrd, %Hr, Hw⟩)
    · isplitl []
      · ileft; ipureintro; exact Hn.1
      · ileft; ipureintro; exact Hn.2
    · isplitl [Hrd]
      · iright; iexists cv, cid, R; iframe Hci Hk Hrd; ipureintro; exact Hr
      · iright; iexact Hw
  icases bigSepL_exists_range _ N $$ Hs with ⟨%xs, %Hl, Hxs⟩
  icases bigSepL_sep_eqv.1 $$ Hxs with ⟨Hel, Hxs⟩
  icases bigSepL_sep_eqv.1 $$ Hxs with ⟨Hr, Hw⟩
  icases Hb $$ %xs [] [Hel] with ⟨H1, H2, H3, H4⟩
  · ipureintro; exact Hl
  · iexact Hel
  iexists _, _, _, _
  iframe H1 H2 H3 H4
  isplitr
  · ipureintro; simp [Hl]
  isplitl [Hr]
  · rw [bigSepL_map]; iexact Hr
  · rw [bigSepL_map]; iexact Hw

end slots

end Perennial.github_com.imdea_software.swiftpaxos
