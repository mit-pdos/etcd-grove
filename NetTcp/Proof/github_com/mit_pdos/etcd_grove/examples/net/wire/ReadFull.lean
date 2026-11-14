/-
The proof of `wire.ReadFull` (`NetTcp/Spec/.../wire/ReadFull.lean`): a loop over `c.Read(buf[n:])`
(`net.Conn.Read.spec`), each read's update made from the caller's accessor (its outcome kept as
`ReadInfo`: `ReadPost` without the end's state, which goes back through the accessor); the
invariant: `n` bytes read, the first `n` of `buf` the bytes after `r` of a prefix `sent` of the
other end's bytes.
-/
module

public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Spec.net.Conn__Read

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem buf_rejoin (buf : GoSlice) (k : w64) (xs ys : List w8) (hx : xs.length = sint.nat k)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z buf.len) :
    slice.slice buf w8 (W64 0) k ↦* xs -∗ slice.slice buf w8 k buf.len ↦* ys -∗
      (buf ↦* (xs ++ ys) : IProp GF) := by
  iintro H1 H2
  iapply (ownSlice_trivial_slice buf (DFrac.own 1) (xs ++ ys)).2
  iapply ownSlice_combine k buf (DFrac.own 1) xs ys (W64 0) buf.len
    ⟨by rw [hx]; word, by decide, hk.1, hk.2⟩ $$ H1 H2

theorem readRes_inj {bs bs' : List w8} {c c' : w64} (h : readRes bs c = readRes bs' c') :
    bs = bs' ∧ c = c' := by
  unfold readRes at h
  obtain ⟨h1, h2⟩ := val.PairV.inj h
  exact ⟨go.intoVal_inj h1, go.intoVal_inj h2⟩

theorem ReadFull.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    ReadFull.spec (GF := GF) (hG := hG) := by
  sorry -- being re-proved over the v2 specs

end proof

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
