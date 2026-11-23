/-
**The raftpb instance's hard-state laws over the registered `raftpb.HardState`** (`pbHsC`,
`RaftModel/PbHardState.lean`), no new trust (the review files `clone-hs-law.md`, `hsown-unmarshal.md` of
2026-11-22 suggested both derivations):

- `walRaftP_cloneHs`: `WalPbIn.CloneHsLaw walRaftP`, from `proto.Clone`'s trust-boundary spec at `pbHsC`
  (`proto.ClonePb.spec`): the clone is the source's content `c` owned (`hsDecC`, `c' = c` since every hard
  state marshals), frozen (`hsOwnC_freeze`, the general-content form of `walRaftHsO_freeze`) into `walHsIn`
  with the source's facts. The law is of a non-nil source (ledger 2026-11-22).
- `walRaftHsO_unmarshal`: `WalHsOwn.unmarshal` at `walRaftU`/`walRaftHsO`, over `MustUnmarshalState`'s
  translated body (`var s raftpb.HardState; pbutil.MustUnmarshalMessage(&s, d); return &s`) and
  `proto.Unmarshal`'s trust-boundary spec at `pbHsC` (`proto.UnmarshalPb.spec`, as
  `pbutil.MustUnmarshalMessagePb.wp_proof` and the entries' `wp_MustUnmarshalMessage_ent` do: the
  main tree's `pbutil.MustUnmarshalMessagePb.spec` module imports `etcdserver/apply`, ~390 modules more than
  this one's cone): the bytes `walDecHs` accepts are `hsEnc (walHsCanon h)`, which decode to that content.
- `walRaftHsO_notNull`: `WalHsOwn.notNull`.

Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.LawsHs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.PbHardState
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Marshal
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import Spec.google_golang_org.protobuf.proto.ClonePb
public import Spec.google_golang_org.protobuf.proto.UnmarshalPb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

/-- **The bytes `walDecHs` accepts** are a canonical encoding. -/
theorem walDecHs_some [GooseExts] {bs : List w8} {h : HardStateM} (hd : walDecHs bs = some h) :
    bs = hsEnc (walHsCanon h) := by
  unfold walDecHs at hd
  split at hd
  · rename_i he
    cases hd
    exact Classical.choose_spec he
  · cases hd

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **An owned hard state freezes** at its content, its unknown fields valid. -/
theorem hsOwnC_freeze (l : Loc) (c : WalHsC) (E : CoPset) (hu : ufWire hsSchema c.uf) :
    hsOwnC (GF := GF) l c ⊢ |={E}=> hsRoC l c := by
  unfold hsOwnC
  iintro ⟨%pt, %pv, %pc, %st, %sc, %us, %Hn, HT, #cT, HV, #cV, HC, #cC, Hst, Hsc, Hus, Huf⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  imod (pbMsg_alloc raftpb.HardState l st sc us c.uf E
      (by rw [show PbGoType.goTy raftpb.HardState = raftpb.HardState.ty from rfl, pbSchemaOf_hardState]
          exact hu)) $$ [Hst Hsc Hus Huf] with #Hpb
  · iframe
  imodintro
  unfold hsRoC hsCells
  iframe Hpb
  iexists pt, pv, pc
  iframe HT cT HV cV HC cC
  ipureintro; exact Hn

/-- **`CloneHsLaw`**, over `proto.Clone`'s trust-boundary spec at the registered `raftpb.HardState`. -/
theorem walRaftP_cloneHs (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG)) :
    WalPbIn.CloneHsLaw (walRaftP (GF := GF)) := by
  intro p h hp
  rw [show (walRaftP (GF := GF)).hsIn = walHsIn from rfl]
  iintro %Φ ⟨#Hpkg, #Hh⟩ HΦ
  iunfold walHsIn at Hh
  icases Hh with (%Hn | ⟨%c, #Hro, %Hc⟩)
  · exact absurd Hn.1 hp
  have hC := wp_Clone pbHsC pbHsC_reg p c
  simp only [pbHsC_ty, pbHsC_roC] at hC
  iapply wp_fupd
  wp_apply hC $$ [Hro] as %l' ⟨%c', Hd, %Hp⟩
  · iexact Hro
  obtain ⟨-, -, hm⟩ := Hp
  have hc : c' = c := hm trivial
  subst hc
  iunfold hsDecC at Hd
  icases Hd with ⟨Ho, %Hu⟩
  imod hsOwnC_freeze l' c' _ Hu $$ Ho with Hro'
  imodintro
  iapply HΦ
  iexists l'
  isplitr
  · ipureintro; rfl
  unfold walHsIn
  iright
  iexists c'
  iframe Hro'
  ipureintro; exact Hc

/-- **`pbutil.MustUnmarshalMessage(&s, d)` into a fresh `raftpb.HardState`, of a canonical hard state's
bytes**: the hard state holds it, owned. -/
theorem wp_MustUnmarshalMessage_hs (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG))
    (l : Loc) (d : GoSlice) (dq : DFrac) (h : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
        (l ↦ (zero_val go_etcd_io.raft.v3.raftpb.HardState) : IProp GF) ∗
        d ↦*{dq} hsEnc (walHsCanon h) }}
      (App (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.HardState.ty) #l)))
        (Val #d))
    {{ RET #(); d ↦*{dq} hsEnc (walHsCanon h) ∗ walRaftHsO l h }} := by
  wp_start as ⟨Hb, Hd⟩
  wp_auto
  have wpU := wp_Unmarshal pbHsC pbHsC_reg d (hsEnc (walHsCanon h)) dq l
  simp only [pbHsC_ty] at wpU
  wp_apply wpU $$ [Hd Hb] as %err ⟨Hd, %Hok, Hdec⟩
  · iframe; simp only [pbHsC, pbHsM]; iexact Hb
  have hu : (pbHsC (GF := GF)).data.ufValid (walHsCanon h) := by
    intro q hq
    simp only [pbHsC, pbHsM] at hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [walHsCanon_uf]
    exact ufWire_nil _
  have he : err = GoInterface.nil := Hok ⟨walHsCanon h, trivial, hu, rfl⟩
  subst he
  wp_auto
  ihave ⟨%c, Hm, %Hc⟩ := Hdec $$ %rfl
  obtain ⟨-, -, -, Heq⟩ := Hc
  have h0 := Heq (walHsCanon h) trivial hu rfl
  subst h0
  iapply HΦ
  iframe Hd
  iunfold hsDecC at Hm
  icases Hm with ⟨Hm, -⟩
  unfold walRaftHsO
  iexact Hm

/-- **`WalHsOwn.unmarshal`** of `walRaftHsO`, over `proto.Unmarshal`'s trust-boundary spec at the
registered `raftpb.HardState` and `MustUnmarshalState`'s body. -/
theorem walRaftHsO_unmarshal (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    ∀ (d : GoSlice) (dq : DFrac) (bs : List w8) (h : HardStateM), walRaftU.decState bs = some h →
      {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ d ↦*{dq} bs }}
        (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.MustUnmarshalState)) (Val #d))
      {{ (p : Loc), RET #p; d ↦*{dq} bs ∗ walRaftHsO p h }} := by
  intro d dq bs h hdec
  have hbs : bs = hsEnc (walHsCanon h) := walDecHs_some hdec
  subst hbs
  wp_start as Hd
  wp_auto
  wp_apply (wp_MustUnmarshalMessage_hs wp_Unmarshal _ d dq h) $$ [Hd s] as ⟨Hd, Hs⟩
  · iframe
  iapply HΦ
  iframe

/-- **`WalHsOwn.notNull`** of `walRaftHsO`. -/
theorem walRaftHsO_notNull (p : Loc) (h : HardStateM) :
    walRaftHsO (GF := GF) p h ⊢ ⌜p ≠ null⌝ := by
  unfold walRaftHsO hsOwnC
  iintro ⟨%pt, %pv, %pc, %st, %sc, %us, %Hn, -⟩
  ipureintro; exact Hn

end laws

end EtcdGrove
end Perennial
