/- Lean-first (no Rocq counterpart). minibolt's crash obligations, as pure lemmas: `CrashOkQ (P1 p) p
Good s` for the states `s` of the database file that `BootMinibolt`'s code passes through.

The core is what P1 says of a crash image's valid meta slot, in the terms the client holds
(`seen_idle_slot`, `seen_writing_slot`): the slot is the durable image's (`D`, which agrees with
the durable bytes the `OsMeta` knows, `m.dur`, and with the clean bytes), or the bytes the client
holds (each of its bytes not clean, when no write is in flight), or the client's write in flight
over them. Changes in flight by others on the file are excluded by `CrashSeenR`: they hold none of
the bytes the client holds, so (on a file the client holds whole) they write nothing.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.CrashGood
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.BootP1
public import Proof.os.CrashFileQ

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- What the crashed state holds of a file the client holds as `m`, and the bytes `bs` from 0
(all of them): the file `f`, its bytes `bs`, the durable bytes `m.dur` knows and the clean ones. -/
theorem seen_file {Q : OsState → OsState → Prop} {p : GoString} {m : OsMeta} {dq : DFrac}
    {bs : List (w8 × Bool)} {ts : List (Nat × TokInfo)} {fo : Option OsFile}
    (hwf : bs.length = m.size) (h : CrashSeenR Q p (some m) [(0, dq, bs)] ts fo) :
    ∃ (st st' : OsState) (f : OsFile), OsCrash st st' ∧ Q st st' ∧ st'.files !! p = some fo ∧
      st.file p = some f ∧ f.cur = bs.map Prod.fst ∧
      (∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → f.durable[j]? = some d) ∧
      (∀ j (hj : j < bs.length), bs[j].2 = true → f.durable[j]? = some bs[j].1) ∧
      ∀ t c, st.inflight !! t = some c → c.path = p → ∃ ti, ti.c = c ∧ ((t, ti) ∈ ts ∨
        (∀ off data, c.kind = .write off data → data = [])) := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hst', hm, hxs, -, htok⟩ := h
  obtain ⟨f, hfp, hmo⟩ := hcoh.meta_some p m hm
  have hf : st.file p = some f := file_eq_some.2 hfp
  have hb : ∀ k (hk : k < bs.length), f.cur[k]? = some bs[k].1 ∧
      (bs[k].2 = true → CleanPhys f k) := by
    intro k hk
    have := hxs (0, dq, bs) List.mem_cons_self k hk
    simp only [Nat.zero_add] at this
    obtain ⟨f1, h1, h2, h3⟩ := hcoh.bytes p k _ this
    rw [hf] at h1; cases h1
    exact ⟨h2, fun hc => (h3 hc).1⟩
  have hcur : f.cur = bs.map Prod.fst := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < bs.length
    · rw [(hb k hk).1, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    · rw [List.getElem?_eq_none (by have := hmo.size; omega),
        List.getElem?_eq_none (by simp; omega)]
  refine ⟨st, st', f, hcr, hQ, hst', hf, hcur, fun j d h => hmo.dur j d h, fun j hj hc => ?_, ?_⟩
  · have h4 := ((hb j hj).2 hc).2.2.2
    rw [h4]; exact (hb j hj).1
  · intro t c ht hcp
    obtain ⟨ti, hti, rfl⟩ := coh_tok hcoh ht
    refine ⟨ti, rfl, ?_⟩
    rcases htok t ti hti hcp with hin | ⟨hq, hd⟩
    · exact Or.inl hin
    · refine Or.inr fun off data hk => ?_
      have hsz : st.size ti.c.path = bs.length := by
        rw [hcp, size_of_file hf, hcur, List.length_map]
      refine Classical.byContradiction fun hne => ?_
      have hlen : 0 < data.length := List.length_pos_iff.2 hne
      by_cases ho : off < bs.length
      · apply hd (0, dq, bs) List.mem_cons_self off ho
        simp only [affRange, affLo, affHi, hk, hsz, Nat.zero_add, List.mem_range'_1]
        omega
      · apply hq
        apply hcoh.tok_q t ti hti
        simp only [Reaches, hk, hsz]
        omega

/-- What a crash may leave of a file the client holds whole as `m`, `bs`, with no write in flight
(`idleImg`): an image within `m`'s size bounds, with the clean bytes of `bs`, whose valid meta
slots are the durable image `D`'s (which agrees with `m.dur` and the clean bytes) or `bs`'s. -/
def idleImg (m : OsMeta) (bs : List (w8 × Bool)) (img D : List w8) : Prop :=
  m.lo ≤ img.length ∧ img.length ≤ m.hi ∧
  (∀ (k : Nat) (x : w8 × Bool), bs[k]? = some x → x.2 = true → img[k]? = some x.1) ∧
  (∀ (j : Nat) (d : w8), m.dur[j]? = some (some d) → D[j]? = some d) ∧
  (∀ j (hj : j < bs.length), bs[j].2 = true → D[j]? = some bs[j].1) ∧
  ∀ i < 2, 4096 * i + 80 ≤ img.length → metaValid (fileMeta img i) →
    metaSlot img i = metaSlot D i ∨ metaSlot img i = metaSlot (bs.map Prod.fst) i

/-- **The idle obligation**: a state without a write in flight is crash-safe under P1 if every
`idleImg` is good, or the file may vanish (it was created since boot) . -/
theorem crashOkQ_idle {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)}
    (hwf : bs.length = m.size) (H : ∀ img D, idleImg m bs img D → goodImg img) :
    CrashOkQ (P1 p) p Good (some (m, bs, none)) := by
  intro fo hfc hseen
  rcases hfc with ⟨rfl, -⟩ | ⟨img, rfl, hlo, hhi, hcl⟩
  · trivial
  obtain ⟨st, st', f, -, hP, hst', hf, hcur, hdur, hclean, htok⟩ := seen_file hwf hseen
  refine H img f.durable ⟨hlo, hhi, fun k x hk hc => ?_, hdur, hclean, fun i hi hlen hv => ?_⟩
  · simpa using hcl _ List.mem_cons_self k x hk hc
  rcases hP f img i hf hst' hi hlen hv with h1 | ⟨-, h2⟩ | ⟨t, off, data, ht, h3⟩
  · exact Or.inl h1
  · exact Or.inr (by rw [h2, hcur])
  · obtain ⟨ti, hc, hin | hnil⟩ := htok t _ ht rfl
    · simp [cToks] at hin
    · have hd := hnil off data rfl
      subst hd
      right; rw [h3, ← hcur]; unfold writeBytes; rw [if_pos rfl]

/-- **Obligation 1**: the file `OpenFile` creates, empty. -/
theorem crashOkQ_create (p : GoString) : CrashOkQ (P1 p) p Good (some (newMeta, [], none)) := by
  apply crashOkQ_idle rfl
  rintro img D ⟨-, hhi, -⟩
  have h0 : img.length = 0 := by simp only [newMeta] at hhi; omega
  refine ⟨by omega, Or.inl ⟨by omega, fun i _ hle => by omega⟩⟩

end pure

end bboltfs
end EtcdGrove
end Perennial
