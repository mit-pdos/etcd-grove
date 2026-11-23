/-
**The raftpb instance's entry codec** (pure; W4c U4 of `notes/wal-fsext-w4c-plan.md`, "W4c U4 log"):
the canonical wire content of an entry (`walEntCanon`: `Term`, `Index`, `Type` set, `Data` nil when
empty, no unknown fields), its bytes (`walEncEnt`: protobuf-go's, `entryEncC`, the registered
`raftpb.Entry`'s encoder, `Proof/go_etcd_io/raft/v3/PbEntryTypeCore.lean`, whose fact
`entryEncC_ok` was the main tree's axiom until 2026-11-23 and is now a theorem, protobuf stage S1),
and the decoder of those bytes (`walDecEnt`).

**Entries of size `2 ^ 48` or more** (which Go cannot allocate, `proto.Marshal`'s `maxAlloc`; the WAL's
`Save` takes entries below `2 ^ 40` bytes) get stand-in bytes, `walEntJunk`: `entryEncC_ok` says
nothing of encodings of `2 ^ 63` bytes or more, so the real encoder's injectivity is not available
there, and `WalUnmarshal.Ok`'s round trip is stated for every entry. The stand-in is longer than every
real encoding of a smaller entry and injective, so `walEncEnt` is injective (`walEncEnt_inj`); it is
also longer than any Go slice (`2 ^ 64` bytes or more, W4c U4 b), so no bytes in memory decode to such
an entry (`walDecEnt_small`: `MustUnmarshalEntry`'s law needs the entry's real encoding).
Lean-first.
-/
module

public import Proof.go_etcd_io.raft.v3.PbEntryTypeCore
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Varint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section codec
variable [GooseExts]

/-- **An entry's canonical wire content** (see the file header). -/
def walEntCanon (e : EntryM) : EntryC :=
  open Classical in
  ⟨some e.Term', some e.Index', some e.Type', if e.Data' = [] then none else some e.Data', []⟩

theorem walEntCanon_model (e : EntryM) : (walEntCanon e).model = e := by
  rcases e with ⟨t, i, ty, d⟩
  unfold walEntCanon EntryC.model
  by_cases h : d = []
  · subst h; simp
  · simp [h]

/-- The canonical content is below Go's allocation limit. -/
def walEntSmall (e : EntryM) : Prop := entrySize (walEntCanon e) < 2 ^ 48

/-- **The stand-in bytes of an entry too large for Go** (see the file header). -/
def walEntJunk (e : EntryM) : List w8 :=
  List.replicate (2 ^ 64) (0 : w8) ++ varintEnc (uint.nat e.Term') ++ varintEnc (uint.nat e.Index') ++
    varintEnc (uint.nat e.Type') ++ e.Data'

/-- **The entry marshaller**: protobuf-go's bytes of the canonical content (see the file header). -/
def walEncEnt (e : EntryM) : List w8 :=
  open Classical in
  if walEntSmall e then entryEncC (walEntCanon e) else walEntJunk e

theorem walEncEnt_small {e : EntryM} (h : walEntSmall e) :
    walEncEnt e = entryEncC (walEntCanon e) ∧ entDecode (walEncEnt e) = some e ∧
      (walEncEnt e).length = entrySize (walEntCanon e) := by
  have hk := entryEncC_ok (walEntCanon e) (ufWire_nil _) (by unfold walEntSmall at h; omega)
  unfold EntWireOk at hk
  rw [walEntCanon_model] at hk
  have he : walEncEnt e = entryEncC (walEntCanon e) := by unfold walEncEnt; rw [if_pos h]
  rw [he]
  exact ⟨rfl, hk.1, hk.2⟩

theorem walEncEnt_big {e : EntryM} (h : ¬ walEntSmall e) : walEncEnt e = walEntJunk e := by
  unfold walEncEnt; rw [if_neg h]

theorem walEntJunk_len (e : EntryM) : 2 ^ 64 ≤ (walEntJunk e).length := by
  unfold walEntJunk; simp only [List.length_append, List.length_replicate]; omega

theorem walEntJunk_inj {e e' : EntryM} (h : walEntJunk e = walEntJunk e') : e = e' := by
  unfold walEntJunk at h
  simp only [List.append_assoc, List.append_cancel_left_eq] at h
  obtain ⟨ht, h⟩ := varintEnc_append_inj _ _ _ _ h
  obtain ⟨hi, h⟩ := varintEnc_append_inj _ _ _ _ h
  obtain ⟨hy, hd⟩ := varintEnc_append_inj _ _ _ _ h
  rcases e with ⟨t, i, ty, d⟩
  rcases e' with ⟨t', i', ty', d'⟩
  simp only at ht hi hy hd
  rw [uint_nat_inj _ _ ht, uint_nat_inj _ _ hi, uint_nat_inj _ _ hy, hd]

/-- **The entry marshaller is injective.** -/
theorem walEncEnt_inj {e e' : EntryM} (h : walEncEnt e = walEncEnt e') : e = e' := by
  by_cases hs : walEntSmall e <;> by_cases hs' : walEntSmall e'
  · have h1 := (walEncEnt_small hs).2.1
    have h2 := (walEncEnt_small hs').2.1
    rw [h] at h1
    exact Option.some.inj (h1.symm.trans h2)
  · exfalso
    have h1 := (walEncEnt_small hs).2.2
    have h2 := walEntJunk_len e'
    rw [h, walEncEnt_big hs'] at h1
    unfold walEntSmall at hs; omega
  · exfalso
    have h1 := (walEncEnt_small hs').2.2
    have h2 := walEntJunk_len e
    rw [← h, walEncEnt_big hs] at h1
    unfold walEntSmall at hs'; omega
  · rw [walEncEnt_big hs, walEncEnt_big hs'] at h
    exact walEntJunk_inj h

/-- **The entry decoder**: the entry whose bytes (`walEncEnt`) `bs` is. -/
def walDecEnt (bs : List w8) : Option EntryM :=
  open Classical in
  if h : ∃ e, bs = walEncEnt e then some (Classical.choose h) else none

theorem walDecEnt_enc (e : EntryM) : walDecEnt (walEncEnt e) = some e := by
  have he : ∃ e', walEncEnt e = walEncEnt e' := ⟨e, rfl⟩
  unfold walDecEnt
  rw [dif_pos he]
  exact congrArg some (walEncEnt_inj (Classical.choose_spec he)).symm

/-- **Bytes the decoder reads as an entry, shorter than any stand-in, are its real encoding.** -/
theorem walDecEnt_small {bs : List w8} {e : EntryM} (h : walDecEnt bs = some e) (hl : bs.length < 2 ^ 64) :
    walEntSmall e ∧ bs = entryEncC (walEntCanon e) := by
  unfold walDecEnt at h
  split at h
  · rename_i hx
    have he : Classical.choose hx = e := Option.some.inj h
    have hb := Classical.choose_spec hx
    rw [he] at hb
    by_cases hs : walEntSmall e
    · exact ⟨hs, hb.trans (walEncEnt_small hs).1⟩
    · exfalso
      rw [walEncEnt_big hs] at hb
      have := walEntJunk_len e
      rw [← hb] at this
      omega
  · cases h

end codec

end EtcdGrove
end Perennial
