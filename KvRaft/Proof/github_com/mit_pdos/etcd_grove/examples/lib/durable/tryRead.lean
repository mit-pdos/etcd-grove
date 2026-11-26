-- The copy for the part `KvRaft/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/tryRead.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Spec/.../examples/lib/durable/tryRead.lean`: by what the name holds under the
handle's physical state. Nothing: `os.Open` fails (`Open.wp_absentErrS`), and `errors.Is(err,
os.ErrNotExist)` answers whether the errno is `ENOENT` (`errors.IsPathErrnoNotExist.spec`, a callee
spec: proved, and passed by the Link). A candidate's file: `os.Open` opens it or fails with an errno other than `ENOENT`
(`Open.wp_fileSN`), so `done` is false; `Stat` gives its size (the candidate's half of its `OsMeta`, in
the handle), one `ReadAt` its contents (the candidate's half of its bytes), and the deferred `Close`
closes it. Lean-first (no Rocq counterpart).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Inv
public import Proof.os.NsFileS
public import Spec.errors.IsPathErrnoNotExist
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Spec.os.File__ReadAt
public import Spec.os.File__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DurFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

theorem openFd_flRO_readable (i : Ino) : (openFd i flRO).readable = true := by
  show decide (flRO.toNat % 4 ≠ O_WRONLY) = true; decide

theorem durSize_nat {c : DCand} (hsz : c.m.size = c.v.length) (hbd : c.v.length < 2 ^ 63) :
    sint.nat (W64 (c.m.size : Int)) = c.v.length := by
  rw [hsz]; word

theorem durSize_nonneg {c : DCand} (hsz : c.m.size = c.v.length) (hbd : c.v.length < 2 ^ 63) :
    0 ≤ sint.Z (W64 (c.m.size : Int)) := by
  rw [hsz]; word
theorem github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead.wp_proof
    (wp_IsNE : errors.IsPathErrnoNotExist.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.specLong (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.etcd_grove.examples.lib.durable.tryRead.spec (GF := GF) (hG := hG) := by
  intro γ f R qc p hf hok
  obtain ⟨s0, hok⟩ := hok
  obtain ⟨hd, hb, htb, hbn, htbn, hlen⟩ := hf
  wp_start as ⟨#Hinv, #Hsi, Hh, Hperm⟩
  iunfold durHandleP at Hh
  icases Hh with ⟨%qd, Hp, Hnb, Hnt, Hcur, Htmp, Hpath⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  unfold DFile.name
  have hNb : (NameSet.only [f.b]).Mem f.b := by simp [NameSet.Mem]
  have hcurIs := hok.curIs
  cases hx : p.hb.cur !! f.b with
  | none =>
    wp_apply os.Open.wp_absentErrS f.d f.b R f.J (.only [f.b]) (DFrac.own qd) (DFrac.own (1 : Qp).half)
      p.hb qc hbn hNb hx $$ [Hinv Hsi Hpath Hnb Hperm] as %fl %err ⟨Hpath, Hnb, Hperm, %e, %he, #Herr⟩
    · iframe; iframe #
    obtain ⟨he0, rfl⟩ := he
    ihave %herr := os.errnoPathErr_ne err e $$ Herr
    ihave ⟨%ee, #Hee⟩ := os.errNotExist_of_pkgInit $$ Hpkg
    ihave #HIs := wp_IsNE err e he0 $$ Hpkg Herr
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    wp_bind (App (App _ (Val #(GoInterface.ok ie))) (Val #ee))
    iunfold errIsNotExist at HIs
    iapply HIs $$ Hee
    inext
    wp_auto
    iapply HΦ
    iframe Hperm
    isplitl [Hp Hnb Hnt Hcur Htmp Hpath]
    · iunfold durHandleP; iexists qd; iframe
    ipureintro
    intro _
    refine ⟨none, ?_, rfl, rfl⟩
    unfold DurPhys.CurIs; rw [hx]
  | some n =>
    cases n with
    | dir J =>
      exfalso; unfold DurPhys.CurIs at hcurIs; rw [hx] at hcurIs; exact hcurIs
    | file i =>
      icases (curRes_file f p i hx).1 $$ Hcur with ⟨%c, %hci, Hcand⟩
      obtain ⟨hc, rfl⟩ := hci
      obtain ⟨hsz, hlo, hhi, hbd⟩ := hok.cands c hc
      iunfold candRes at Hcand
      icases Hcand with ⟨Hm, Hby⟩
      wp_apply os.Open.wp_fileSN f.d f.b R f.J c.i (.only [f.b]) (DFrac.own qd) (DFrac.own (1 : Qp).half)
        p.hb qc hbn hNb hx $$ [Hinv Hsi Hpath Hnb Hperm] as %fl %err ⟨Hpath, Hnb, Hperm, Hres⟩
      · iframe; iframe #
      icases Hres with (⟨%fd, %hfd, Hf, Hoff, Hfd⟩ | ⟨%e, %he, #Herr⟩)
      · obtain ⟨rfl, hfd0⟩ := hfd
        have hrd : (openFd c.i flRO).readable = true := openFd_flRO_readable c.i
        (try wp_auto)
        wp_apply wp_Stat fl fd (child f.d f.b) (DFrac.own 1) (DFrac.own 1) (DFrac.own (1 : Qp).half)
          (openFd c.i flRO) c.m $$ [Hinv Hf Hfd Hm] as %fi %err2 ⟨Hf, Hfd, Hm, Hfi, -, -⟩
        · iframe; iframe #
        icases Hfi with (⟨%fs, %Hfi, Hfs⟩ | %Hfi)
        rotate_left
        · obtain ⟨Herr, rfl, -⟩ := Hfi
          cases err2 with
          | nil => exact absurd rfl Herr
          | ok ie =>
          (try wp_auto)
          wp_apply wp_Close fl fd (child f.d f.b) (openFd c.i flRO) $$ [Hinv Hf Hfd] as %e3 -
          · iframe; iframe #; iapply lockToks_unlocked <;> rfl
          (try wp_auto)
          iapply HΦ
          iframe Hperm
          isplitl [Hp Hnb Hnt Hm Hby Htmp Hpath]
          · iunfold durHandleP; iexists qd; iframe
            iapply (curRes_file f p c.i hx).2
            iexists c
            iunfold candRes
            iframe
            ipureintro; exact ⟨hc, rfl⟩
          ipureintro
          intro h; cases h
        obtain ⟨rfl, rfl⟩ := Hfi
        (try wp_auto)
        wp_apply wp_Size fs (W64 c.m.size) $$ [Hfs] as -
        · iexact Hfs
        have hsz' : sint.nat (W64 (c.m.size : Int)) = c.v.length := durSize_nat hsz hbd
        (try wp_auto)
        wp_apply (wp_slice_make2 (V := w8) (W64 c.m.size)) as %buf ⟨Hbuf, -⟩
        · ipureintro; exact durSize_nonneg hsz hbd
        (try wp_auto)
        wp_apply wp_ReadAt fl fd (child f.d f.b) (DFrac.own 1) buf
            (List.replicate (sint.nat (W64 c.m.size)) (zero_val w8)) (W64 0) (DFrac.own 1)
            (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) (openFd c.i flRO) c.m (c.v.map durB) hrd
            (by decide)
            (by rw [List.length_replicate, hsz']; show 0 + c.v.length < 2 ^ 63; omega)
            (by rw [List.length_replicate, hsz']; show 0 + c.v.length ≤ c.m.size; omega)
            (by rw [List.length_replicate, hsz', List.length_map])
            $$ [Hinv Hf Hbuf Hfd Hm Hby] as %n %err3 ⟨Hf, Hfd, Hm, Hby, %vs', Hbuf, %Hres, -⟩
        · iframe; iframe #
        obtain ⟨-, ⟨rfl, rfl, hvs'⟩ | hne⟩ := Hres
        rotate_left
        · cases err3 with
          | nil => exact absurd rfl (by first | exact hne | exact hne.1)
          | ok ie =>
          (try wp_auto)
          wp_apply wp_Close fl fd (child f.d f.b) (openFd c.i flRO) $$ [Hinv Hf Hfd] as %e3 -
          · iframe; iframe #; iapply lockToks_unlocked <;> rfl
          (try wp_auto)
          iapply HΦ
          iframe Hperm
          isplitl [Hp Hnb Hnt Hm Hby Htmp Hpath]
          · iunfold durHandleP; iexists qd; iframe
            iapply (curRes_file f p c.i hx).2
            iexists c
            iunfold candRes
            iframe
            ipureintro; exact ⟨hc, rfl⟩
          ipureintro
          intro h; cases h
        have hv : vs' = c.v := by rw [hvs']; simp [List.map_map, Function.comp_def]
        subst hv
        (try wp_auto)
        wp_apply wp_bytes_to_string buf c.v (DFrac.own 1) $$ Hbuf as Hbuf
        (try wp_auto)
        wp_apply wp_Close fl fd (child f.d f.b) (openFd c.i flRO) $$ [Hinv Hf Hfd] as %e3 -
        · iframe; iframe #; iapply lockToks_unlocked <;> rfl
        (try wp_auto)
        iapply HΦ
        iframe Hperm
        isplitl [Hp Hnb Hnt Hm Hby Htmp Hpath]
        · iunfold durHandleP; iexists qd; iframe
          iapply (curRes_file f p c.i hx).2
          iexists c
          iunfold candRes
          iframe
          ipureintro; exact ⟨hc, rfl⟩
        ipureintro
        intro _
        refine ⟨some c.v, ?_, rfl, rfl⟩
        unfold DurPhys.CurIs; rw [hx]
        exact ⟨c, hc, rfl, rfl⟩
      · obtain ⟨he0, hne, rfl⟩ := he
        ihave %herr := os.errnoPathErr_ne err e $$ Herr
        ihave ⟨%ee, #Hee⟩ := os.errNotExist_of_pkgInit $$ Hpkg
        ihave #HIs := wp_IsNE err e he0 $$ Hpkg Herr
        cases err with
        | nil => exact absurd rfl herr
        | ok ie =>
        (try wp_auto)
        wp_bind (App (App _ (Val #(GoInterface.ok ie))) (Val #ee))
        iunfold errIsNotExist at HIs
        iapply HIs $$ Hee
        inext
        rw [decide_eq_false hne]
        wp_auto
        iapply HΦ
        iframe Hperm
        isplitl [Hp Hnb Hnt Hm Hby Htmp Hpath]
        · iunfold durHandleP; iexists qd; iframe
          iapply (curRes_file f p c.i hx).2
          iexists c
          iunfold candRes
          iframe
          ipureintro; exact ⟨hc, rfl⟩
        ipureintro
        intro h; cases h

end proof

end EtcdGrove
end Perennial
