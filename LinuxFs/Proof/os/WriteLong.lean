/-
The proof of `Spec/os/WriteLong.lean` (`os.File.WriteAt.specLong`). Up to `maxRW` (1 GiB) it is
`File__WriteAt.lean`'s spec (one chunk: `A = len(b)`, `PwOut` is `PwOutA` with everything
announced). **Past 1 GiB: `sorry`** (2026-11-13, `wal-bridge`): the model's loop then writes chunks
of `maxRW` from where the last attempt stopped, each announcing its own range; the proof is
`File__WriteAt.lean`'s Löb induction with the invariant generalized to "a write of `data` that
announced its first `A` bytes and wrote its first `j`" (`osMeta (pwPost m off A j)`,
`PwOutA m off data A j xs ys`), the bytes and cells split in three around each chunk, and two pure
steps generalizing `pwPost_step`/`pwOut_step` to an announcement `[off + nn, off + A')` with
`A ≤ A'` (the crash low bound composes because `m.lo ≤ m.size`). Lean-first.
-/
module

public import LinuxFs.Proof.os.File__WriteAt
public import LinuxFs.Spec.os.WriteLong

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `PwOut` is `PwOutA` with everything announced. -/
theorem os.PwOut.pwOutA {m : OsMeta} {off : Nat} {data : List w8} {j : Nat} {xs ys : List ByteG}
    (h : os.PwOut m off data j xs ys) : os.PwOutA m off data data.length j xs ys := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨h1, c0, extra, h2, h3, h4, h5⟩ := h.2 i hi
  exact ⟨h1, c0, extra, h2, fun _ => h3, h4, h5⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.WriteAt.wp_proof_long : os.File.WriteAt.specLong (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hwr hoff hgap hbig hn hlo hxl
  by_cases hsmall : data.length ≤ 0x40000000
  · iintro %Φ Hpre HΦ
    iapply (os.File.WriteAt.wp_proof (GF := GF) (hG := hG) f fd name dqf sl data dqs off dq d m xs
      hwr hoff hgap hbig hn hsmall hxl) $$ Hpre
    iintro !> %n %err ⟨Hf, Hsl, Hfd, %j, %ys, %Hr, Hm, Hbs, Hmc, Hok⟩
    iapply HΦ
    iframe Hf Hsl Hfd
    iexists j, data.length, ys
    iframe Hm Hbs Hmc Hok
    ipureintro
    obtain ⟨hj, hout, hcut, hres⟩ := Hr
    exact ⟨hj, Nat.le_refl _, fun _ => rfl, os.PwOut.pwOutA hout, hcut, hres⟩
  · -- past `maxRW`: the chunked loop (see the file header)
    sorry

end proof

end EtcdGrove
end Perennial
