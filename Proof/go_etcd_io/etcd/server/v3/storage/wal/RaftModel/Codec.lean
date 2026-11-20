/-
**The raftpb instance's codec for snapshots and hard states** (pure; W4c U4 of
`notes/wal-fsext-w4c-plan.md`, "W4c U4 log"): the canonical wire content of each model the WAL's
marshaller parameter `Mr` writes, its encoding, and the decoders `U` reads them back with.

- **Snapshots** (`walpb.Snapshot`): `walSnapCanon m al`, `Index` and `Term` set, the conf state nil when
  it is the zero one (`walCsZero`, what `Create`'s `snapC0` has) and else set with `AutoLeave` set when
  `al` or `AutoLeave` is true (`walAlC`: the presence bit of the history's `.snap m al`, wal-link Hm1
  route (B), 2026-11-19), no unknown fields; its bytes are `snapEnc` (the registered `walpb.Snapshot`'s transparent encoder,
  `walpb/PbSnapshot.lean`). `walDecSnap` returns the index and term of the canonical snapshot a byte
  list encodes (`walSnapCanon_enc_idTerm`: they are determined, the encoding starting with two
  varint fields).
- **Hard states** (`raftpb.HardState`, three proto2 `optional uint64`s, `raft.proto:101-105`):
  `WalHsC` its wire content, `hsEnc` the bytes protobuf-go writes for it (tags 1, 2, 3, then the
  unknown fields; **the trusted fact that protobuf-go writes these bytes does not exist yet**:
  `raftpb.HardState` is not a registered type, `PbSchema.lean`, so no `proto` spec covers it; U4 log),
  `walHsCanon h` the canonical content (all nil when empty, as `&raftpb.HardState{}` is; else all set,
  as raft's `hardState()` builds it, `raft.go:504-510`), `walDecHs` the decoder of canonical
  encodings (`walHsCanon_enc_inj`), and the encoding's bound (`walHsCanon_enc_len`: at most 33 bytes).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncFold
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Varint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3 WalEnc

section codec
variable [GooseExts]

/-! ## Snapshots -/

/-- **An `AutoLeave` pointer's content** (wal-link Hm1 route (B), 2026-11-19): set to `b` when the
presence bit `al` is set or `b` is true (a nil pointer reads `false`), else nil. -/
def walAlC (al b : Bool) : Option Bool := if al || b then some b else none

theorem walAlC_getD (al b : Bool) : (walAlC al b).getD false = b := by
  unfold walAlC; cases al <;> cases b <;> rfl

/-- A conf state's canonical content: its lists, `AutoLeave` as `walAlC al`, no unknown fields. -/
def walCsCanon (cs : ConfStateM) (al : Bool) : WalCsC :=
  ⟨cs.Voters', cs.Learners', cs.VotersOutgoing', cs.LearnersNext', walAlC al cs.AutoLeave', []⟩

/-- **A snapshot metadata's canonical `walpb.Snapshot` content** (see the file header). -/
def walSnapCanon (m : SnapshotMetadataM) (al : Bool) : WalSnapC :=
  open Classical in
  ⟨some m.Index', some m.Term',
    if m.ConfState' = walCsZero then none else some (walCsCanon m.ConfState' al), []⟩

theorem walSnapCanon_model (m : SnapshotMetadataM) (al : Bool) : (walSnapCanon m al).model = m := by
  rcases m with ⟨⟨v, l, vo, ln, a⟩, i, t⟩
  unfold walSnapCanon WalSnapC.model
  by_cases h : (⟨v, l, vo, ln, a⟩ : ConfStateM) = walCsZero
  · simp only [h, if_pos, Option.map_none, Option.getD_none, Option.getD_some]
  · simp only [h, if_neg, not_false_eq_true, Option.map_some, Option.getD_some, walCsCanon,
      WalCsC.model, walAlC_getD]

theorem walSnapCanon_levels (m : SnapshotMetadataM) (al : Bool) :
    ∀ p ∈ (walSnapCanon m al).levels, ufWire p.1 p.2 := by
  intro p hp
  unfold walSnapCanon WalSnapC.levels at hp
  split at hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; exact ufWire_nil _
  · simp only [walCsCanon, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ufWire_nil _

/-- **The canonical snapshot's bytes determine its index and term.** -/
theorem walSnapCanon_enc_idTerm (m m' : SnapshotMetadataM) (al al' : Bool)
    (h : snapEnc (walSnapCanon m al) = snapEnc (walSnapCanon m' al')) :
    m.Index' = m'.Index' ∧ m.Term' = m'.Term' := by
  unfold snapEnc walSnapCanon at h
  simp only [Option.map_some, optVarintField, List.append_assoc] at h
  obtain ⟨-, h⟩ := varintEnc_append_inj _ _ _ _ h
  obtain ⟨hi, h⟩ := varintEnc_append_inj _ _ _ _ h
  obtain ⟨-, h⟩ := varintEnc_append_inj _ _ _ _ h
  obtain ⟨ht, -⟩ := varintEnc_append_inj _ _ _ _ h
  exact ⟨uint_nat_inj _ _ hi, uint_nat_inj _ _ ht⟩

/-- **The snapshot decoder**: the index and term of the canonical snapshot `bs` encodes. -/
def walDecSnap (bs : List w8) : Option (w64 × w64) :=
  open Classical in
  if h : ∃ m al, bs = snapEnc (walSnapCanon m al) then
    some ((Classical.choose h).Index', (Classical.choose h).Term')
  else none

theorem walDecSnap_enc (m : SnapshotMetadataM) (al : Bool) :
    walDecSnap (snapEnc (walSnapCanon m al)) = some (m.Index', m.Term') := by
  have he : ∃ m' al', snapEnc (walSnapCanon m al) = snapEnc (walSnapCanon m' al') := ⟨m, al, rfl⟩
  unfold walDecSnap
  rw [dif_pos he]
  obtain ⟨h1, h2⟩ := walSnapCanon_enc_idTerm _ _ _ _ (Classical.choose_spec (Classical.choose_spec he))
  rw [← h1, ← h2]

/-- `Create`'s snapshot is canonical. -/
theorem walSnapCanon_snapC0 (al : Bool) : walSnapCanon snapC0.model al = snapC0 := by
  simp [walSnapCanon, snapC0, WalSnapC.model]

/-! ## Hard states -/

/-- **A `raftpb.HardState`'s wire content**: `Term`, `Vote`, `Commit` nil or set, the unknown
fields. -/
structure WalHsC where
  term : Option w64
  vote : Option w64
  commit : Option w64
  uf : List w8
deriving DecidableEq

/-- What the getters read. -/
def WalHsC.model (c : WalHsC) : HardStateM :=
  ⟨c.term.getD (W64 0), c.vote.getD (W64 0), c.commit.getD (W64 0)⟩

/-- **The bytes protobuf-go writes for a `raftpb.HardState` holding `c`** (fields in number order,
then the unknown fields; see the file header: not yet a trusted fact). -/
def hsEnc (c : WalHsC) : List w8 :=
  optVarintField 1 (c.term.map uint.nat) ++ optVarintField 2 (c.vote.map uint.nat) ++
    optVarintField 3 (c.commit.map uint.nat) ++ c.uf

/-- The content of `&raftpb.HardState{}`. -/
def walHsC0 : WalHsC := ⟨none, none, none, []⟩

/-- **A hard state's canonical content** (see the file header). -/
def walHsCanon (h : HardStateM) : WalHsC :=
  if hsEmptyP h then walHsC0 else ⟨some h.Term', some h.Vote', some h.Commit', []⟩

theorem walHsCanon_model (h : HardStateM) : (walHsCanon h).model = h := by
  rcases h with ⟨t, v, c⟩
  unfold walHsCanon
  split
  · rename_i he
    obtain ⟨h1, h2, h3⟩ := he
    simp only at h1 h2 h3
    subst h1 h2 h3; rfl
  · rfl

theorem hsEmptyP_eq {h : HardStateM} (he : hsEmptyP h) : h = hsZero := by
  rcases h with ⟨t, v, c⟩
  obtain ⟨h1, h2, h3⟩ := he
  simp only at h1 h2 h3
  subst h1 h2 h3; rfl

private theorem varintEnc_ne_nil (n : Nat) (r : List w8) : varintEnc n ++ r ≠ [] := by
  obtain ⟨x, t, hx⟩ := varintEnc_cons n
  rw [hx]; simp

/-- **The canonical encoding is injective.** -/
theorem walHsCanon_enc_inj (h h' : HardStateM)
    (he : hsEnc (walHsCanon h) = hsEnc (walHsCanon h')) : h = h' := by
  unfold walHsCanon at he
  by_cases e : hsEmptyP h <;> by_cases e' : hsEmptyP h' <;>
    simp only [e, e', if_pos, if_neg, not_false_eq_true] at he
  · rw [hsEmptyP_eq e, hsEmptyP_eq e']
  · exfalso
    simp only [hsEnc, walHsC0, Option.map_some, Option.map_none, optVarintField, List.append_nil,
      List.nil_append, List.append_assoc] at he
    exact varintEnc_ne_nil _ _ he.symm
  · exfalso
    simp only [hsEnc, walHsC0, Option.map_some, Option.map_none, optVarintField, List.append_nil,
      List.nil_append, List.append_assoc] at he
    exact varintEnc_ne_nil _ _ he
  · simp only [hsEnc, Option.map_some, optVarintField, List.append_assoc, List.append_nil] at he
    obtain ⟨-, he⟩ := varintEnc_append_inj _ _ _ _ he
    obtain ⟨ht, he⟩ := varintEnc_append_inj _ _ _ _ he
    obtain ⟨-, he⟩ := varintEnc_append_inj _ _ _ _ he
    obtain ⟨hv, he⟩ := varintEnc_append_inj _ _ _ _ he
    obtain ⟨-, he⟩ := varintEnc_append_inj _ _ _ _ he
    have hc := varintEnc_inj (by simpa using he)
    rcases h with ⟨t, v, c⟩
    rcases h' with ⟨t', v', c'⟩
    simp only at ht hv hc
    rw [uint_nat_inj _ _ ht, uint_nat_inj _ _ hv, uint_nat_inj _ _ hc]

/-- **The hard-state decoder**: the hard state whose canonical encoding `bs` is. -/
def walDecHs (bs : List w8) : Option HardStateM :=
  open Classical in
  if h : ∃ hs, bs = hsEnc (walHsCanon hs) then some (Classical.choose h) else none

theorem walDecHs_enc (h : HardStateM) : walDecHs (hsEnc (walHsCanon h)) = some h := by
  have he : ∃ h', hsEnc (walHsCanon h) = hsEnc (walHsCanon h') := ⟨h, rfl⟩
  unfold walDecHs
  rw [dif_pos he]
  exact congrArg some (walHsCanon_enc_inj _ _ (Classical.choose_spec he)).symm

private theorem optVarintField_len (num : Nat) (o : Option w64) (hn : num < 16) :
    (optVarintField num (o.map uint.nat)).length ≤ 11 := by
  rcases o with _ | v
  · simp [optVarintField]
  · simp only [Option.map_some, optVarintField, List.length_append]
    have h1 := varintEnc_length_le 1 (num * 8) (by omega) (by omega)
    have h2 := varintEnc_length_w64 (uint.nat v) (by have := v.isLt; simp [uint.nat]; omega)
    omega

/-- **The canonical encoding's bound**: at most 33 bytes. -/
theorem walHsCanon_enc_len (h : HardStateM) : (hsEnc (walHsCanon h)).length ≤ 33 := by
  have hu : (walHsCanon h).uf = [] := by unfold walHsCanon; split <;> rfl
  unfold hsEnc
  rw [hu]
  simp only [List.length_append, List.length_nil]
  have := optVarintField_len 1 (walHsCanon h).term (by omega)
  have := optVarintField_len 2 (walHsCanon h).vote (by omega)
  have := optVarintField_len 3 (walHsCanon h).commit (by omega)
  omega

private theorem repVarintField_len (num : Nat) (hn : num < 16) (vs : List w64) :
    (repVarintField num vs).length ≤ 11 * vs.length := by
  induction vs with
  | nil => simp [repVarintField]
  | cons v vs ih =>
    unfold repVarintField at ih ⊢
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := varintEnc_length_le 1 (num * 8) (by omega) (by omega)
    have h2 := varintEnc_length_w64 (uint.nat v) (by have := v.isLt; simp [uint.nat]; omega)
    omega

/-- (wal-link L3, F2, 2026-11-19) **The canonical snapshot's encoding's bound**: with fewer than `2^32` ids in
its conf state, below `2^40` bytes (layer 1's record bound). -/
theorem walSnapCanon_enc_len (m : SnapshotMetadataM) (al : Bool)
    (h : m.ConfState'.Voters'.length + m.ConfState'.Learners'.length +
      m.ConfState'.VotersOutgoing'.length + m.ConfState'.LearnersNext'.length < 2 ^ 32) :
    (snapEnc (walSnapCanon m al)).length < 2 ^ 40 := by
  have hi := optVarintField_len 1 (some m.Index') (by omega)
  have ht := optVarintField_len 2 (some m.Term') (by omega)
  have hc : ∀ o : Option WalCsC, (∀ c, o = some c → (csEnc c).length ≤ 11 * 2 ^ 32 + 2) →
      (optBytesField 3 (o.map csEnc)).length ≤ 11 * 2 ^ 32 + 13 := by
    intro o ho
    rcases o with _ | c
    · simp [optBytesField]
    · have hc := ho c rfl
      simp only [Option.map_some, optBytesField, List.length_append]
      have h1 := varintEnc_length_le 1 (3 * 8 + 2) (by omega) (by omega)
      have h2 := varintEnc_length_w64 (csEnc c).length (by omega)
      omega
  have hcs : ∀ c, (walSnapCanon m al).confState = some c → (csEnc c).length ≤ 11 * 2 ^ 32 + 2 := by
    intro c hc
    unfold walSnapCanon at hc
    split at hc
    · cases hc
    · cases hc
      unfold csEnc walCsCanon walAlC
      have r1 := repVarintField_len 1 (by omega) m.ConfState'.Voters'
      have r2 := repVarintField_len 2 (by omega) m.ConfState'.Learners'
      have r3 := repVarintField_len 3 (by omega) m.ConfState'.VotersOutgoing'
      have r4 := repVarintField_len 4 (by omega) m.ConfState'.LearnersNext'
      have a1 := varintEnc_length_le 1 (5 * 8) (by omega) (by omega)
      have a2 := varintEnc_length_le 1 (if m.ConfState'.AutoLeave' = true then 1 else 0) (by omega)
        (by split <;> omega)
      split <;> simp only [Option.map_some, Option.map_none, optVarintField, List.length_append,
        List.length_nil] <;> omega
  have hb := hc _ hcs
  unfold snapEnc
  have hu : (walSnapCanon m al).uf = [] := by unfold walSnapCanon; rfl
  have hix : (walSnapCanon m al).index = some m.Index' := rfl
  have htx : (walSnapCanon m al).term = some m.Term' := rfl
  rw [hu, hix, htx]
  simp only [List.length_append, List.length_nil]
  omega

end codec

end EtcdGrove
end Perennial
