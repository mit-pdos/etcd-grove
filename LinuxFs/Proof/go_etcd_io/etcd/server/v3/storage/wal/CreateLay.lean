/- Lean-first (no Rocq counterpart).

# The fresh WAL's layout (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", eighteenth session; pure)

What the invariant holds of the WAL `Create` commits (`walCreate_osAUnc`'s `habs`): one segment `g`
(named `walFileName 0 0`), no cuts, the stream `createStream Mr md` written and synced, zeros past it
(`old` all zeros, `z0 = 0`, so that `TailLast`'s last clause holds and `tailStop` is vacuous).

* `createLay`: the layout.
* `createLay_abs`: its static relation `WalAbsD` over a directory whose `.wal` entries are `g` alone.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateHdr
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- **The fresh WAL's layout**: the area's inode `jr`, the name `nm`, the directory `J`, the one
segment `g`, its stream `L` bytes long, written and synced. -/
def createLay (jr : Ino) (nm : GoString) (J : Ino) (g : SegG) (L : Nat) : WalLay :=
  ⟨jr, nm, J, [], 0, [g], List.replicate g.bs.length 0, L, L, 0⟩

/-- The fresh WAL's records are the header records from CRC 0. -/
theorem create_recsOfSegs (Mr : WalMarshal) (md : List w8) :
    recsOfSegs walCodec Mr (walDurFresh md).metadata (segsOf (histM (walDurFresh md)) []) =
      chainRecs walCodec 0#32 (hdrDs Mr md) := by
  simp [recsOfSegs, segsDs, segsOf, histM, walDurFresh, segHdrDs]

/-- **The fresh layout's static relation** (`walCreate_osAUnc`'s `habs`): the segment `g` named
`walFileName 0 0`, its bytes the stream then zeros, durable, its `OsMeta` half exact; the directory's
`.wal` entries `g` alone. -/
theorem createLay_abs (Mr : WalMarshal) (md : List w8) (hMr : WalMarshalCreateOk Mr)
    (hmd : md.length < 2 ^ 41) (jr : Ino) (nm : GoString) (J : Ino) (g : SegG) (ents : Ents)
    (hname : g.name = walFileName 0 0)
    (hbs : g.bs = (createStream Mr md ++
      List.replicate (g.bs.length - (createStream Mr md).length) 0).map durB ∧
      (createStream Mr md).length ≤ g.bs.length)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hents : walInos ents = [g.ino]) :
    WalAbsD walCodec Mr (walDurFresh md)
      (createLay jr nm J g (createStream Mr md).length) ents := by
  have hpos := createStream_pos Mr md hMr
  have hfit := createStream_fit Mr md hMr hmd
  have hS : segStream walCodec Mr (walDurFresh md) [] 0 = createStream Mr md := rfl
  have hgb : ∀ b (h : b < g.bs.length), g.bs[b] = durB ((createStream Mr md).getD b 0) := by
    intro b h
    obtain ⟨hbs1, hbs2⟩ := hbs
    generalize hS' : createStream Mr md = S at hbs1 hbs2 ⊢
    rw [List.getElem_of_eq hbs1 h, List.getElem_map]
    have hl := congrArg List.length hbs1
    simp only [List.length_map, List.length_append, List.length_replicate] at hl
    by_cases hb : b < S.length
    · rw [List.getElem_append_left hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
      rfl
    · rw [List.getElem_append_right (by omega), List.getElem_replicate,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  refine
    { names := ?_, cuts := ?_, nameBound := ?_, cut := ?_, metas := ?_, intact := ?_,
      last := ?_, synced := ?_, lastSynced := ?_, fit := ?_, tailStop := ?_, nonempty := ?_,
      cutPos := ?_ }
  · simp [createLay, hents]
  · simp [createLay]
  · intro k g' hk
    simp only [createLay] at hk ⊢
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨0, 0, hname, by decide, fun h => absurd h (by omega)⟩
    | succ k => simp at hk
  · simp [createLay, walDurFresh, segStart]
  · intro g' hg'
    simp only [createLay, List.mem_singleton] at hg'
    subst hg'
    exact ⟨hmeta.1, hmeta.2.1, Nat.le_of_eq hmeta.2.2.1, Nat.le_of_eq hmeta.2.2.2.symm,
      Or.inr hmeta.2.2⟩
  · intro k g' hk _
    simp [createLay] at hk
  · intro g' hg'
    simp only [createLay, List.getLast?_singleton, Option.some.injEq] at hg'
    subst hg'
    refine ⟨fun _ => ?_, fun hne => absurd hmeta.2.2 hne⟩
    simp only [TailLast, createLay, List.length_nil, List.length_replicate, hS]
    refine ⟨Nat.le_refl _, Nat.le_refl _, by simp, hbs.2, fun b x hx => ?_, Nat.zero_le _, by simp,
      fun _ b _ hb => by simp [List.getD_eq_getElem?_getD, hb]⟩
    have hb : b < g.bs.length := (List.getElem?_eq_some_iff.1 hx).1
    have hxe : x = g.bs[b] := ((List.getElem?_eq_some_iff.1 hx).2).symm
    rw [hxe, hgb b hb]
    unfold ByteOk
    by_cases hbw : b < (createStream Mr md).length
    · simp [hbw]
    · simp only [hbw, decide_false, Bool.false_eq_true, ite_false]
      have : (createStream Mr md).getD b 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [this]
      refine ⟨[], ?_, by simp, fun _ => rfl, ?_⟩ <;>
        simp [List.getD_eq_getElem?_getD, hb]
  · refine ⟨by simp [walDurFresh], ?_⟩
    simp only [createLay, List.length_nil]
    exact Nat.le_of_eq (by simp [walDurFresh]; rfl)
  · simp [createLay, segStart, walDurFresh]
  · simp only [createLay]
    rw [create_recsOfSegs]
    apply recsFit_of_frames
    rw [← createStream_recs]; omega
  · intro hz0
    simp only [createLay, List.length_nil, hS] at hz0
    omega
  · simp [createLay]
  · simp [createLay]

end pure

end WalFs
end EtcdGrove
end Perennial
