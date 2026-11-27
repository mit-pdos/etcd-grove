/-
**The server's instance of the WAL's raft messages and codec** (wal-link L1b, option (iii) as decided by
etcd-grove-03, 2026-11-17: `notes/wal-link-handoff.md`, "L1b by (iii)"). The raftpb instance
(`walRaftP`/`walRaftMr`, `RaftModel/Pb.lean`, `Marshal.lean`) reads canonical contents only; the server
saves the entries raft hands it, whose wire contents are not a function of their models (an entry received
in a `MsgApp` keeps any unknown fields, `ufWire`; a proposal's `Type` is unset). So:

- **Entries, by a model wrap.** The WAL-level model of an entry content `c` is `walEntW c`: `c`'s term,
  index and type, and as its `Data'` the bytes protobuf-go writes for `c` (`entryEncC c`). The marshaller
  `walEncEntW` returns those bytes for such a wrap (`walEntWOk`), and the stand-in `walEntJunk` otherwise;
  it is injective because the bytes determine the model (`entryEncC_ok`), so no injectivity of `entryEncC`
  on contents is needed. The WAL's history holds wrapped models; the server reads them back through
  `walEntUnwrap` (the entry's model).
- **Hard states, canonical.** raft hands out canonical hard states (`hsOptC`, raft's `hardState()`), so the
  instance's hard states are the raftpb instance's (`walHsIn`: `nil` and zero, or the canonical content
  unless empty), and the snapshot and state codecs are `walRaftMr`'s.

`walSrvP` (the objects), `walSrvMr`/`walSrvU` (the codec), and their laws (`walSrvPb_laws`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Laws
public import Proof.go_etcd_io.raft.v3.InvPbLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

section pure
variable [GooseExts]

/-- **The WAL-level model of an entry content** (see the file header): its term, index and type, and
the bytes protobuf-go writes for it. -/
def walEntW (c : EntryC) : EntryM := ⟨c.model.Term', c.model.Index', c.model.Type', entryEncC c⟩

/-- **The entry a WAL-level model stands for**: its term and index, and the type and data its bytes
decode to (`entDecode`); the model itself if they do not decode. Keeps the index and the term
(`walEntUnwrap_index`), so the WAL's fold commutes with it (`walFoldChkFrom_map`). -/
def walEntUnwrap (e : EntryM) : EntryM :=
  match entDecode e.Data' with
  | some m => ⟨e.Term', e.Index', m.Type', m.Data'⟩
  | none => e

theorem walEntUnwrap_index (e : EntryM) : (walEntUnwrap e).Index' = e.Index' := by
  unfold walEntUnwrap; split <;> rfl

theorem walEntUnwrap_term (e : EntryM) : (walEntUnwrap e).Term' = e.Term' := by
  unfold walEntUnwrap; split <;> rfl

/-- **A wrap of a content the WAL can marshal** (valid unknown fields, not empty, below Go's allocation
limit). -/
def walEntWOk (e : EntryM) : Prop :=
  ∃ c : EntryC, ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 48 ∧ e = walEntW c

theorem walEntW_enc {c : EntryC} (hu : ufWire entrySchema c.uf) (hs : entrySize c < 2 ^ 48) :
    entDecode (entryEncC c) = some c.model ∧ (entryEncC c).length = entrySize c :=
  entryEncC_ok c hu (by omega)

/-- A wrap stands for its content's model. -/
theorem walEntUnwrap_W {c : EntryC} (hu : ufWire entrySchema c.uf) (hs : entrySize c < 2 ^ 48) :
    walEntUnwrap (walEntW c) = c.model := by
  have h := (walEntW_enc hu hs).1
  unfold walEntUnwrap
  rw [show (walEntW c).Data' = entryEncC c from rfl, h]
  rfl

/-- A wrap keeps its content's index and term. -/
theorem walEntW_index (c : EntryC) : (walEntW c).Index' = c.model.Index' := rfl
theorem walEntW_term (c : EntryC) : (walEntW c).Term' = c.model.Term' := rfl

/-- **The server's entry marshaller** (see the file header). -/
def walEncEntW (e : EntryM) : List w8 :=
  open Classical in
  if walEntWOk e then e.Data' else walEntJunk e

theorem walEncEntW_W {c : EntryC} (hu : ufWire entrySchema c.uf) (hp : 0 < entrySize c)
    (hs : entrySize c < 2 ^ 48) : walEncEntW (walEntW c) = entryEncC c := by
  unfold walEncEntW
  rw [if_pos ⟨c, hu, hp, hs, rfl⟩]
  rfl

theorem walEncEntW_ok_len {e : EntryM} (h : walEntWOk e) : (walEncEntW e).length < 2 ^ 48 := by
  obtain ⟨c, hu, hp, hs, rfl⟩ := h
  rw [walEncEntW_W hu hp hs, (walEntW_enc hu hs).2]; exact hs

theorem walEncEntW_bad {e : EntryM} (h : ¬ walEntWOk e) : walEncEntW e = walEntJunk e := by
  unfold walEncEntW; rw [if_neg h]

/-- **The server's entry marshaller is injective**: a wrap's bytes determine its model
(`entryEncC_ok`), hence the wrap. -/
theorem walEncEntW_inj {e e' : EntryM} (h : walEncEntW e = walEncEntW e') : e = e' := by
  by_cases hs : walEntWOk e <;> by_cases hs' : walEntWOk e'
  · obtain ⟨c, hu, hp, hz, rfl⟩ := hs
    obtain ⟨c', hu', hp', hz', rfl⟩ := hs'
    rw [walEncEntW_W hu hp hz, walEncEntW_W hu' hp' hz'] at h
    have h1 := (walEntW_enc hu hz).1
    have h2 := (walEntW_enc hu' hz').1
    rw [h, h2, Option.some.injEq] at h1
    unfold walEntW
    rw [h, h1]
  · exfalso
    have h1 := walEncEntW_ok_len hs
    have h2 := walEntJunk_len e'
    rw [h, walEncEntW_bad hs'] at h1
    omega
  · exfalso
    have h1 := walEncEntW_ok_len hs'
    have h2 := walEntJunk_len e
    rw [← h, walEncEntW_bad hs] at h1
    omega
  · rw [walEncEntW_bad hs, walEncEntW_bad hs'] at h
    exact walEntJunk_inj h

/-- **The server's entry decoder**: the WAL-level model whose bytes (`walEncEntW`) `bs` is. -/
def walDecEntW (bs : List w8) : Option EntryM :=
  open Classical in
  if h : ∃ e, bs = walEncEntW e then some (Classical.choose h) else none

theorem walDecEntW_enc (e : EntryM) : walDecEntW (walEncEntW e) = some e := by
  have he : ∃ e', walEncEntW e = walEncEntW e' := ⟨e, rfl⟩
  unfold walDecEntW
  rw [dif_pos he]
  exact congrArg some (walEncEntW_inj (Classical.choose_spec he)).symm

/-- **Bytes the server's decoder reads as an entry, shorter than any stand-in, are a wrap's bytes.** -/
theorem walDecEntW_small {bs : List w8} {e : EntryM} (h : walDecEntW bs = some e) (hl : bs.length < 2 ^ 64) :
    ∃ c : EntryC, ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 48 ∧ e = walEntW c ∧
      bs = entryEncC c := by
  unfold walDecEntW at h
  split at h
  · rename_i hx
    have he : Classical.choose hx = e := Option.some.inj h
    have hb := Classical.choose_spec hx
    rw [he] at hb
    by_cases hs : walEntWOk e
    · obtain ⟨c, hu, hp, hz, rfl⟩ := hs
      exact ⟨c, hu, hp, hz, rfl, hb.trans (walEncEntW_W hu hp hz)⟩
    · exfalso
      rw [walEncEntW_bad hs] at hb
      have := walEntJunk_len e
      rw [← hb] at this
      omega
  · cases h

/-- **The server's marshaller** (see the file header): `walRaftMr` but for entries. -/
def walSrvMr : WalMarshal := { walRaftMr with encEntry := walEncEntW }

/-- **The server's unmarshaller**: `walRaftU` but for entries. -/
def walSrvU : WalUnmarshal := { walRaftU with decEntry := walDecEntW }

theorem walSrvU_ok : walSrvU.Ok walSrvMr where
  entry e := walDecEntW_enc e
  state := walRaftU_ok.state
  snap := walRaftU_ok.snap
  snap0 := walRaftU_ok.snap0

theorem walSrvU_snapCoh : walSrvU.SnapCoh := walRaftU_snapCoh

theorem walSrvMr_createOk : WalMarshalCreateOk walSrvMr := walRaftMr_createOk

theorem walSrvMr_encState_lt (hs : HardStateM) : (walSrvMr.encState hs).length < 2 ^ 32 :=
  walRaftMr_encState_lt hs

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The server's entries** (`P.entIn`): a frozen entry at a content `c` whose wrap is `e`, with valid
unknown fields, not empty (its encoding is not empty: `MustMarshalMessage` returns a non-`nil` slice;
an entry of index above 0 has its `Index` set), below Go's allocation limit. -/
def walEntInW (l : Loc) (e : EntryM) : IProp GF :=
  iprop(∃ c : EntryC, entRoC l c ∗
    ⌜e = walEntW c ∧ ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 48⌝)

instance walEntInW_persistent (l : Loc) (e : EntryM) : Persistent (walEntInW (GF := GF) l e) := by
  unfold walEntInW; infer_instance

/-- **The server's raft messages**: its entries (`walEntInW`), the raftpb instance's hard states. -/
def walSrvP : WalPbIn GF where
  hsIn := walHsIn
  entIn := walEntInW
  hsIn_persistent := walHsIn_persistent
  entIn_persistent := walEntInW_persistent

theorem walSrvP_hsIn : (walSrvP (GF := GF)).hsIn = (walRaftP (GF := GF)).hsIn := rfl

/-- **A canonical `nil`-or-read-only hard state** (raft's `Ready`'s, `hsOptC`) is the instance's. -/
theorem walHsIn_of_hsOptC (p : Loc) (h : HardStateM) : (hsOptC p h : IProp GF) ⊢ walHsIn p h := by
  iintro #H
  iunfold hsOptC at H
  unfold walHsIn
  icases H with (⟨%Hp, %Hh⟩ | H)
  · ileft; ipureintro; exact ⟨Hp, by rw [Hh]⟩
  iunfold hsROC at H
  icases H with ⟨%pt, %pv, %pc, %Hnn, #HT, #cT, #HV, #cV, #HC, #cC, #Hpb⟩
  iright
  by_cases he : hsEmptyP h
  · iexists (⟨some h.Term', some h.Vote', some h.Commit', []⟩ : WalHsC)
    isplitl
    · unfold hsRoC hsCells
      isplitl
      · iexists pt, pv, pc
        isplitr; · ipureintro; exact Hnn
        iframe HT HV HC
        simp only [optCell]
        iframe cT cV cC
      · iexact Hpb
    · ipureintro; exact ⟨rfl, .inl he⟩
  · iexists walHsCanon h
    have hc : walHsCanon h = ⟨some h.Term', some h.Vote', some h.Commit', []⟩ := by
      unfold walHsCanon; rw [if_neg he]
    isplitl
    · rw [hc]
      unfold hsRoC hsCells
      isplitl
      · iexists pt, pv, pc
        isplitr; · ipureintro; exact Hnn
        iframe HT HV HC
        simp only [optCell]
        iframe cT cV cC
      · iexact Hpb
    · ipureintro; exact ⟨walHsCanon_model h, .inr rfl⟩

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`GetIndexLaw`.** -/
theorem walSrvP_getIndex : WalPbIn.GetIndexLaw (walSrvP (GF := GF)) := by
  intro l e
  rw [show (walSrvP (GF := GF)).entIn = walEntInW from rfl]
  wp_start_folded as #He
  unfold walEntInW
  icases He with ⟨%c, #Hc, %Hce⟩
  obtain ⟨rfl, -⟩ := Hce
  wp_apply (wp_entRoC_GetIndex l c) $$ []
  · iexact Hc
  rw [show (walEntW c).Index' = c.index.getD (W64 0) from rfl]
  iapply HΦ; ipureintro; trivial

/-- **`GetTermLaw`.** -/
theorem walSrvP_getTerm : WalPbIn.GetTermLaw (walSrvP (GF := GF)) := by
  intro l e
  rw [show (walSrvP (GF := GF)).entIn = walEntInW from rfl]
  wp_start_folded as #He
  unfold walEntInW
  icases He with ⟨%c, #Hc, %Hce⟩
  obtain ⟨rfl, -⟩ := Hce
  wp_apply (wp_entRoC_GetTerm l c) $$ []
  · iexact Hc
  rw [show (walEntW c).Term' = c.term.getD (W64 0) from rfl]
  iapply HΦ; ipureintro; trivial

/-- **`MarshalEntLaw`**, over `proto.Marshal`'s trust-boundary spec at the registered `raftpb.Entry`. -/
theorem walSrvP_marshalEnt (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG)) :
    WalPbIn.MarshalEntLaw (walSrvP (GF := GF)) walSrvMr := by
  intro l e
  simp only [walSrvP]
  wp_start as #He
  unfold walEntInW
  icases He with ⟨%c, #Hro, %Hce⟩
  obtain ⟨rfl, hu, hpos, hs⟩ := Hce
  have henc := walEncEntW_W hu hpos hs
  have hlen := (walEntW_enc hu hs).2
  wp_auto
  have wpM := wp_Marshal pbEntryC pbEntryC_reg l c trivial hs
  simp only [pbEntryC_ty, pbEntryC_roC, pbEncC_pbEntryC] at wpM
  wp_apply wpM $$ [] as %d ⟨Hd, Hcap, -⟩
  · iframe #
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hd
  iapply HΦ
  simp only [walSrvMr]
  rw [henc]
  iframe
  ipureintro
  rintro rfl
  rw [← hlen, Hlen.1] at hpos
  simp [slice.nil] at hpos

/-- **`SizeLaw`** (`Save`'s pre-lock check, fix 0009), over `proto.Size`'s trust-boundary spec at the
registered `raftpb.Entry`. -/
theorem walSrvP_size (wp_Size : proto.SizePb.spec (GF := GF) (hG := hG)) :
    WalPbIn.SizeLaw (walSrvP (GF := GF)) walSrvMr := by
  intro l e
  rw [show (walSrvP (GF := GF)).entIn = walEntInW from rfl]
  wp_start_folded as #He
  iunfold walEntInW at He
  icases He with ⟨%c, #Hro, %Hce⟩
  obtain ⟨rfl, hu, hpos, hs⟩ := Hce
  have henc := walEncEntW_W hu hpos hs
  have hlen := (walEntW_enc hu hs).2
  have wpS := wp_Size pbEntryC pbEntryC_reg l c
  simp only [pbEntryC_ty, pbEntryC_roC, pbEntryC_size] at wpS
  wp_apply wpS $$ [] as %n %Hn
  · iframe #
  iapply HΦ
  ipureintro
  simp only [walSrvMr]
  rw [henc, hlen]
  exact Hn

/-- **`pbutil.MustUnmarshalMessage(e, d)` into a fresh `raftpb.Entry`, of a content's bytes** (valid
unknown fields): the entry holds that content, owned (`proto.Unmarshal`'s decoded content is the only
one with those bytes). -/
theorem wp_MustUnmarshalMessage_entC (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG))
    (l : Loc) (d : GoSlice) (dq : DFrac) (c : EntryC) (hu : ufWire entrySchema c.uf) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
        (l ↦ (zero_val go_etcd_io.raft.v3.raftpb.Entry) : IProp GF) ∗
        d ↦*{dq} entryEncC c }}
      (App (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty) #l)))
        (Val #d))
    {{ RET #(); d ↦*{dq} entryEncC c ∗ entPtsCC l (DFrac.own 1) c }} := by
  wp_start as ⟨Hb, Hd⟩
  wp_auto
  have wpU := wp_Unmarshal pbEntryC pbEntryC_reg d (entryEncC c) dq l
  simp only [pbEntryC_ty] at wpU
  wp_apply wpU $$ [Hd Hb] as %err ⟨Hd, %Hok, Hdec⟩
  · iframe; simp only [pbEntryC, pbEntryM]; iexact Hb
  have hu' : (pbEntryC (GF := GF)).data.ufValid c := by
    simp only [pbEntryC_ufValid]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hu
  have he : err = GoInterface.nil := Hok ⟨c, trivial, hu', rfl⟩
  subst he
  wp_auto
  ihave ⟨%c1, Hm, %Hc⟩ := Hdec $$ %rfl
  obtain ⟨-, -, -, Heq⟩ := Hc
  have h0 := Heq c trivial hu' rfl
  subst h0
  iapply HΦ
  iframe

/-- **`UnmarshalEntLaw`**, over `proto.Unmarshal`'s trust-boundary spec at the registered
`raftpb.Entry`. -/
theorem walSrvP_unmarshalEnt (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    WalPbIn.UnmarshalEntLaw (walSrvP (GF := GF)) walSrvU := by
  intro d dq bs e hdec
  simp only [walSrvP]
  wp_start as Hd
  ihave %Hlen := ownSlice_len _ _ _ $$ Hd
  obtain ⟨c, hu, hp, hs, rfl, hbs⟩ := walDecEntW_small hdec (by rw [Hlen.1]; word)
  subst hbs
  iapply wp_fupd
  wp_auto
  wp_apply (wp_MustUnmarshalMessage_entC wp_Unmarshal _ d dq c hu) $$ [Hd e] as ⟨Hd, He⟩
  · iframe
  imod entPtsCC_freeze _ _ _ $$ He with #He
  imodintro
  iapply HΦ
  iframe Hd
  unfold walEntInW
  iexists c
  iframe He
  ipureintro
  exact ⟨rfl, hu, hp, hs⟩

/-- **The server's instance's laws** (`MarshalHsLaw`, `CloneHsLaw` and `WalHsOwn` are not among them, as for
the raftpb instance, `RaftModel/Laws.lean`; `MarshalHsLaw` is `walSrvP_marshalHs`, `LawsHsMarshal.lean`). -/
theorem walSrvPb_laws : WalPbLaws (walSrvP (GF := GF)) walSrvMr walSrvU where
  nil := walRaftP_nil
  zero := walRaftP_zero
  mustSync := walRaftP_mustSync
  isEmpty := walRaftP_isEmpty
  getIndex := walSrvP_getIndex
  getTerm := walSrvP_getTerm
  marshalEnt := walSrvP_marshalEnt proto.MarshalPb.wp_proof
  size := walSrvP_size proto.SizePb.wp_proof
  unmarshalEnt := walSrvP_unmarshalEnt proto.UnmarshalPb.wp_proof
  uOk := walSrvU_ok
  snapCoh := walSrvU_snapCoh
  createOk := walSrvMr_createOk
  encState := walSrvMr_encState_lt

end laws

end EtcdGrove
end Perennial
