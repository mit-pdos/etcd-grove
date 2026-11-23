/-
**A `*bufio.Writer` holding nothing** (net/http's server, 2026-11-23: the writers of its pools,
`newBufioWriterSize`/`putBufioWriter`, and of a connection before its first response, which
`Hijack` resets): `bufio.rawWriter bw sz` is the writer's struct with a buffer of `sz > 0` bytes
and nothing buffered (`n` zero), its destination and error any; `bufio.writerRep_raw`: a fresh
writer's fields (`bufio.writerRep … [] err`, `NewWriterSize`'s) are one. Lean-first.
-/
module

public import Proof.bufio.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
def bufio.rawWriter (bw : Loc) (sz : Nat) : IProp GF :=
  iprop(∃ (v : _root_.Perennial.bufio.Writer) (bs : List w8), bw ↦ v ∗ v.buf' ↦* bs ∗
    ⌜bs.length = sz ∧ 0 < sz ∧ v.n' = W64 0⌝)

/-- A writer's fields holding nothing (`bufio.writerRep`, what `NewWriterSize` returns,
`bufio.NewWriterSize.specRep`) are a raw writer. -/
theorem bufio.writerRep_raw (bw : Loc) (wi : GoInterfaceOk) (Ew : GoInterface → IProp GF)
    (sz : Nat) (err : GoInterface) :
    bufio.writerRep bw wi Ew sz [] err ⊢ bufio.rawWriter bw sz := by
  unfold bufio.writerRep bufio.rawWriter
  iintro ⟨%buf, %n, %rest, Hb, Hbuf, %Hn, -⟩
  obtain ⟨hn, hpos, hsz⟩ := Hn
  simp only [List.nil_append, List.length_nil] at hn hpos hsz
  rw [List.nil_append]
  iexists _, rest
  iframe Hb Hbuf
  ipureintro
  refine ⟨hsz, by omega, ?_⟩
  show n = W64 0
  word

end defs

end EtcdGrove
end Perennial
