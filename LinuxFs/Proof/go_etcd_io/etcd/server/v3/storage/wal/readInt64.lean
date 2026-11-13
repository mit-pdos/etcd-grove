/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/readInt64.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readInt64
public import Spec.io.ReadFull
public import Spec.encoding.binary.ReadInt64LE

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.readInt64.wp_proof
    (HRF : io.ReadFull.spec (GF := GF) (hG := hG))
    (HRead : binary.ReadInt64LE.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.readInt64.spec (GF := GF) (hG := hG) := by
  intro ri S E r0 eof ueof
  iintro #Hrs
  wp_start as ⟨#Heof, #Hueof, HS⟩
  ihave #Hinit := encoding.binary.isInit_access $$ Hpkg2
  icases Hinit with ⟨#HLE, -⟩
  ihave #HI := io.isInit_access $$ Hpkg
  icases HI with ⟨-, -, -, -, -, #HU, -⟩
  iunfold errors.newVar at HU
  icases HU with ⟨%x, #Hx, -⟩
  icombine Hueof Hx gives %hu
  have hun : ueof ≠ GoInterface.nil := by rw [hu]; simp [interface.mkOk]
  wp_auto
  wp_apply HRead (r := GoInterface.ok ri) (P := S r0)
    (Q := fun ys _ err => iprop(⌜io.readFullOk E eof ueof r0 ys 8 err⌝ ∗ S (r0 ++ ys)))
    $$ [] [HS n] as %err ⟨%ys, %nv, ⟨%Hok, HS⟩, Hn⟩
  · imodintro
    iintro %sl %xs
    imodintro
    iintro %Φ' ⟨Hsl, %Hxs, HS⟩ HΦ'
    wp_apply HRF ri S E r0 sl xs eof ueof $$ Hrs [Hsl HS] as %n' %err' ⟨%ys, %Hys, Hsl, HS⟩
    · iframe
      isplitl []
      · iexact Heof
      · iexact Hueof
    iapply HΦ'
    iexists ys
    iframe
    ipureintro
    rw [Hxs] at Hys
    refine ⟨⟨Hys.2.1, ?_⟩, Hys.2.2⟩
    intro he
    rcases Hys.2.2 with ⟨h, _⟩ | ⟨h, e, he', _, h1, h2⟩
    · exact h
    · exfalso
      by_cases hc : e = eof ∧ ys ≠ []
      · exact hun (h1 hc ▸ he)
      · exact he' (h2 hc ▸ he)
  · iframe
  icases Hn with (⟨⟨%He, %Hl⟩, Hn⟩ | ⟨%He, Hn⟩)
  · wp_auto
    iapply HΦ
    iexists ys
    iframe
    ipureintro
    exact ⟨Hok, fun _ => rfl⟩
  · wp_auto
    iapply HΦ
    iexists ys
    iframe
    ipureintro
    exact ⟨Hok, fun h => absurd h He⟩

end proof

end EtcdGrove
end Perennial
